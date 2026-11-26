module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
open GlobalTheory.CompanionTheory.WaveAll

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Swap

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (X : Mat n) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro x hx
  have h1 : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h3 : fderiv ℝ (c • f) x = c • fderiv ℝ f x := (h1.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, Pi.smul_apply, h3]
  rfl

theorem Eu_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_csmul hf c _ hx]
  rw [smul_comm c (1 / 2 : ℂ), smul_add c, smul_comm c]

theorem Epow_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (c • f)) (c • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Eu_congr isOpen_GLs (ih d b) s a d hx]
    exact Eu_csmul (Epow_smooth hR hf s m d b) c s a d hx

theorem gel_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (c • f)) (c • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_csmul hR hf c s m a a hx

theorem gel_add (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  have e : f + f' = f - (-1 : ℂ) • f' := by
    ext y
    simp
  have hm : ContDiffOn ℝ ∞ ((-1 : ℂ) • f') (GLs n) := hf'.const_smul (-1 : ℂ)
  have h := gel_sub hR hf hm s m hx
  rw [e, h]
  simp only [Pi.sub_apply, Pi.add_apply, gel_csmul hR hf' (-1) s m hx, Pi.smul_apply]
  simp

theorem gel_zero (hR : RCalc) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (0 : Mat n → V)) 0 (GLs n) := by
  intro x hx
  have h := gel_csmul hR (contDiffOn_const (c := (0 : V)) : ContDiffOn ℝ ∞ (0 : Mat n → V) (GLs n)) 0 s m hx
  simpa using h

theorem gel_sum (hR : RCalc) {ι : Type} (S : Finset ι) {F : ι → Mat n → V}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (∑ i ∈ S, F i)) (∑ i ∈ S, gel s m (F i)) (GLs n) := by
  classical
  intro x hx
  induction S using Finset.induction_on with
  | empty => simpa using gel_zero hR s m hx
  | insert i S hi ih =>
    have hS : ContDiffOn ℝ ∞ (∑ j ∈ S, F j) (GLs n) := by
      have e : (∑ j ∈ S, F j) = fun y => ∑ j ∈ S, F j y := by
        ext y
        simp only [Finset.sum_apply]
      rw [e]
      exact ContDiffOn.sum fun j _ => hF j
    rw [Finset.sum_insert hi, Finset.sum_insert hi, gel_add hR (hF i) hS s m hx, Pi.add_apply, Pi.add_apply, ih]

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ContDiffOn ℝ ∞ (gel s m f) (GLs n) := by
  have e : gel s m f = fun x => ∑ a, Epow s m a a f x := by
    ext x
    simp only [gel, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => Epow_smooth hR hf s m a a

theorem zOp_smooth (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact gel_smooth hR ih p.1 p.2

theorem Eu_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (a b : Fin n)
    (s : Bool) (m : ℕ) : Set.EqOn (Eu s' a b (gel s m f)) (gel s m (Eu s' a b f)) (GLs n) := by
  intro x hx
  have hc := (hR n).1 V f hf
  have hS := hc.1
  have hG := hc.2.2.1
  set d : ℂ := if s' then -Complex.I else Complex.I with hd
  have hdB : ContDiffOn ℝ ∞ (d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).const_smul d
  have hsum : ContDiffOn ℝ ∞ (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).add hdB
  have e : Eu s' a b f = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) := rfl
  rw [e, gel_csmul hR hsum _ s m hx, Pi.smul_apply, gel_add hR (hS _) hdB s m hx, Pi.add_apply,
    gel_csmul hR (hS _) d s m hx, Pi.smul_apply, ← hG s m _ x hx, ← hG s m _ x hx]
  rfl

theorem Epow_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s' m' a b (gel s m f)) (gel s m (Epow s' m' a b f)) (GLs n) := by
  induction m' with
  | zero =>
    intro a b x hx
    by_cases hab : a = b
    · simp [Epow, hab]
    · simp only [Epow, if_neg hab]
      exact (gel_zero hR s m hx).symm
  | succ m' ih =>
    intro a b x hx
    have e : Epow s' (m' + 1) a b f = ∑ c, Eu s' a c (Epow s' m' c b f) := rfl
    rw [e, gel_sum hR _ (fun c => Eu_smooth hR (Epow_smooth hR hf s' m' c b) s' a c) s m hx]
    simp only [Epow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr isOpen_GLs (ih c b) s' a c hx]
    exact Eu_gel hR (Epow_smooth hR hf s' m' c b) s' a c s m hx

theorem gel_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) : Set.EqOn (gel s' m' (gel s m f)) (gel s m (gel s' m' f)) (GLs n) := by
  intro x hx
  have e : gel s' m' f = ∑ a, Epow s' m' a a f := rfl
  rw [e, gel_sum hR _ (fun a => Epow_smooth hR hf s' m' a a) s m hx]
  simp only [gel, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Epow_gel hR hf s' m' s m a a hx
  simpa only [gel, Finset.sum_apply] using h

theorem zOp_append (w w' : List (Bool × ℕ)) (f : Mat n → V) : zOp (w ++ w') f = zOp w (zOp w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change gel p.1 p.2 (zOp (w ++ w') f) = gel p.1 p.2 (zOp w (zOp w' f))
    rw [ih]

theorem gel_zOp (hR : RCalc) (s : Bool) (m : ℕ) (w : List (Bool × ℕ)) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (gel s m (zOp w f)) (zOp w (gel s m f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel s m (gel p.1 p.2 (zOp w f)) x = gel p.1 p.2 (zOp w (gel s m f)) x
    rw [gel_gel hR (zOp_smooth hR w hf) s m p.1 p.2 hx]
    exact gel_congr isOpen_GLs ih p.1 p.2 hx

theorem zOp_zOp (hR : RCalc) (w w' : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (zOp w (zOp w' f)) (zOp w' (zOp w f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel p.1 p.2 (zOp w (zOp w' f)) x = zOp w' (gel p.1 p.2 (zOp w f)) x
    rw [gel_congr isOpen_GLs ih p.1 p.2 hx]
    exact gel_zOp hR p.1 p.2 w' (zOp_smooth hR w hf) hx

theorem zOp_swap : RCalc → ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w w' : List (Bool × ℕ)) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, zOp (w ++ w') f x = zOp (w' ++ w) f x := by
  intro hR n V _ _ w w' f hf x hx
  rw [zOp_append, zOp_append]
  exact zOp_zOp hR w w' hf hx

end GlobalTheory.CompanionTheory.WaveMult.Swap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem isOpenEmbedding_valG (n : ℕ) : Topology.IsOpenEmbedding (Units.val : G n → Mat n) :=
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def coords {n : ℕ} (M : Mat n) : Idx n → ℝ :=
  fun p => if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem cm_apply {n : ℕ} (t : Idx n → ℝ) (i j : Fin n) :
    cm t i j = (t (true, i, j) : ℂ) + (t (false, i, j) : ℂ) * Complex.I := by
  simp only [cm, bs, Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  have key : ∀ f : Fin n → Fin n → ℂ, (∑ x, ∑ y, if x = i ∧ y = j then f x y else 0) = f i j := by
    intro f
    simp [ite_and, Finset.sum_ite_eq']
  simp [Matrix.single_apply, Finset.sum_add_distrib, key]

def cmE (n : ℕ) : (Idx n → ℝ) ≃ₗ[ℝ] Mat n where
  toFun := cm
  map_add' s t := by simp [cm, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [cm, mul_smul, Finset.smul_sum]
  invFun := coords
  left_inv t := by
    funext ⟨b, i, j⟩
    cases b <;> simp [coords, cm_apply]
  right_inv M := by
    ext i j
    simp [coords, cm_apply, Complex.re_add_im]

instance locallyCompactSpace_G (n : ℕ) : LocallyCompactSpace (G n) :=
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).locallyCompactSpace
instance secondCountableTopology_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).isEmbedding.secondCountableTopology

def aH (n : ℕ) : (Idx n → ℝ) ≃ₜ Mat n :=
  (cmE n).toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft (1 : Mat n))

open scoped GroundTheory.Automorphic ENNReal
local instance (priority := high) instMeasGLUnits (n : ℕ) : MeasurableSpace (GL (Fin n) ℂ) := Units.instMeasurableSpace

def mu0 (n : ℕ) : Measure (Mat n) := Measure.map (cmE n) volume

instance isAddHaarMeasure_pushforward (n : ℕ) : (mu0 n).IsAddHaarMeasure :=
  (cmE n).toContinuousLinearEquiv.isAddHaarMeasure_map volume

theorem map_aH (n : ℕ) : Measure.map (aH n) volume = mu0 n := by
  have h1 : Measurable (cmE n) := (cmE n).toContinuousLinearEquiv.continuous.measurable
  have h2 : Measurable (fun x : Mat n => (1 : Mat n) + x) := (continuous_const.add continuous_id).measurable
  have : (aH n : (Idx n → ℝ) → Mat n) = (fun x : Mat n => (1 : Mat n) + x) ∘ (cmE n) := rfl
  rw [this, ← Measure.map_map h2 h1]
  exact map_add_left_eq_self (mu0 n) 1

theorem lint_chart {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) :
    ∫⁻ t in Q, g (1 + cm t) = ∫⁻ x in aH n '' Q, g x ∂(mu0 n) := by
  have hemb := (aH n).measurableEmbedding
  rw [← map_aH, hemb.restrict_map, hemb.lintegral_map,
    Set.preimage_image_eq _ (aH n).injective]
  rfl

theorem lint_haar {n : ℕ} (g : Mat n → ℝ≥0∞) (S : Set (G n)) (hS : MeasurableSet S) :
    ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) =
      ∫⁻ x in Units.val '' S, GroundTheory.Automorphic.haarDensityGLComplex x * g x ∂(mu0 n) := by
  have hemb := GroundTheory.Automorphic.measurableEmbedding_val_GLComplex (n := Fin n)
  have hV : Measure.map Units.val ((GroundTheory.Automorphic.haarGLComplex (mu0 n)).restrict S) =
      ((mu0 n).restrict (Units.val '' S)).withDensity GroundTheory.Automorphic.haarDensityGLComplex := by
    have hVm : MeasurableSet (Units.val '' S) := hemb.measurableSet_image.2 hS
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.restrict_apply (hemb.measurable hs),
      GroundTheory.Automorphic.haarGLComplex_apply, ← restrict_withDensity hVm,
      Measure.restrict_apply hs, Set.image_preimage_inter]
  rw [← hemb.lintegral_map, hV,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      GroundTheory.Automorphic.measurable_haarDensityGLComplex
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  rfl

theorem lint_core {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) (B : ℝ) (hB0 : 0 < B)
    (hB : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ B) :
    ∫⁻ t in Q, g (1 + cm t) ≤
      ENNReal.ofReal B * ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) := by
  have hV : MeasurableSet (Units.val '' S) :=
    (hS.image Units.continuous_val).isClosed.measurableSet
  rw [lint_chart, lint_haar g S hS.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ x in aH n '' Q, g x ∂(mu0 n) ≤ ∫⁻ x in Units.val '' S, g x ∂(mu0 n) := by
        refine lintegral_mono_set ?_
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨y, hy, e⟩ := h t ht
        exact ⟨y, hy, e⟩
    _ ≤ _ := by
        refine setLIntegral_mono' hV ?_
        rintro _ ⟨y, hy, rfl⟩
        have hd : (y : Mat n).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
        have hpos : 0 < (‖(y : Mat n).det‖ ^ 2) ^ n := by positivity
        have h1 : 1 ≤ ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n) := by
          rw [GroundTheory.Automorphic.haarDensityGLComplex, ← ENNReal.ofReal_mul hB0.le,
            ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Fintype.card_fin, inv_pow, ← div_eq_mul_inv, one_le_div hpos]
          exact hB y hy
        calc g y.val = 1 * g y.val := (one_mul _).symm
          _ ≤ (ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n)) * g y.val := by
              gcongr
          _ = _ := mul_assoc _ _ _

theorem dom_units (n : ℕ) (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hQ : IsCompact Q) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  have hH := Measure.isMulLeftInvariant_eq_smul (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ
  set κ := Measure.haarScalarFactor (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ with hκ
  have hcont : Continuous (fun y : G n => (‖(y : Mat n).det‖ ^ 2) ^ n) :=
    (((Units.continuous_val.matrix_det).norm.pow _).pow _)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  have hB1 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB2 : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ max B 1 := fun y hy =>
    ((le_abs_self _).trans (by simpa using hB y hy)).trans (le_max_left _ _)
  refine ⟨max B 1 * κ, by positivity, fun φ hφ h0 => ?_⟩
  have hmem : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y =>
    ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hf : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val hmem
  have hint2 : IntegrableOn (fun y : G n => φ y.val) S μ := hf.continuousOn.integrableOn_compact hS
  have hint1 : IntegrableOn (fun t => φ (1 + cm t)) Q := by
    refine ContinuousOn.integrableOn_compact hQ ?_
    refine hφ.comp (aH n).continuous.continuousOn ?_
    intro t ht
    obtain ⟨y, _, e⟩ := h t ht
    show 1 + cm t ∈ GLs n
    rw [← e]
    exact hmem y
  have key := lint_core (fun x => ENNReal.ofReal (φ x)) Q S hS h (max B 1) hB1 hB2
  rw [hH, Measure.restrict_smul, lintegral_smul_measure,
    ← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun _ => h0 _),
    ← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun _ => h0 _)] at key
  have hR : 0 ≤ ∫ y in S, φ y.val ∂μ := integral_nonneg fun _ => h0 _
  have e : ENNReal.ofReal (max B 1) * κ • ENNReal.ofReal (∫ y in S, φ y.val ∂μ) =
      ENNReal.ofReal (max B 1 * κ * ∫ y in S, φ y.val ∂μ) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB1.le, ENNReal.smul_def,
      ENNReal.ofReal_coe_nnreal, smul_eq_mul, mul_assoc]
  rw [e] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end GlobalTheory.CompanionTheory.SobGL.HaarDom

namespace GlobalTheory.CompanionTheory.SobGL


open scoped GroundTheory.Automorphic in
theorem lebesgue_le_haar :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  intro n m hB μ hμ Q S hQ hS h
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    GroundTheory.Automorphic.matrixMeasurableSpaceComplex
  have e : m = Units.instMeasurableSpace := by
    exact hB.measurable_eq.trans
      (GroundTheory.Automorphic.borelSpace_GLComplex (n := Fin n)).measurable_eq.symm
  subst e
  exact HaarDom.dom_units n μ Q S hQ hS h

end GlobalTheory.CompanionTheory.SobGL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparisonStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_chart_integral_comparison : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | exact GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | (intros; apply GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZOpAvg

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

def Sm (U : ℝ → Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)

section Gen

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_slice {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {t : ℝ} {x : E} (hx : x ∈ S) :
    HasFDerivAt (U t) ((fderiv ℝ (Function.uncurry U) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, x) :=
    (hU.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    hasFDerivAt_prodMk_right t x
  exact hd.hasFDerivAt.comp x hi

theorem gen_sm {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {c : E → E} (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t x => fderiv ℝ (U t) x (c x)) (Set.univ ×ˢ S) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), c p.2)) :=
    contDiff_const.prodMk (hc.comp contDiff_snd)
  have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
    ContDiffOn.fderiv_of_isOpen hU (isOpen_univ.prod hS) (by simp)
  have h2 := h0.clm_apply h1.contDiffOn
  refine h2.congr ?_
  rintro ⟨t, x⟩ ⟨-, hx⟩
  simp [Function.uncurry, (fderiv_slice hS hU hx).fderiv]

theorem int_real {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {φ : ℝ → W} (hφ : Continuous φ) : Integrable (fun t => g t • φ t) := by
  refine Continuous.integrable_of_hasCompactSupport (hg.smul hφ) ?_
  exact hgc.smul_right

theorem gen_avg [ProperSpace E] [CompleteSpace W] {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {x : E} (hx : x ∈ S) (v : E) :
    fderiv ℝ (fun x' => ∫ t, g t • U t x') x v = ∫ t, g t • fderiv ℝ (U t) x v := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hx)
  have hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hcU : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ S) := hU.continuousOn
  have hsl : ∀ y ∈ S, Continuous (fun t => U t y) := fun y hy =>
    hcU.comp_continuous (f := fun t : ℝ => (t, y)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hy⟩)
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (U p.1) p.2) (Set.univ ×ˢ S) := by
    have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen hU hSo (by simp)
    have h1 : ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Set.univ ×ˢ S) :=
      h0.continuousOn.clm_comp continuousOn_const
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (fderiv_slice hS hU hy).fderiv
  obtain ⟨T, hT⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ) T ×ˢ Metric.closedBall x r) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hDc.mono (Set.prod_mono (Set.subset_univ _) hball))
  have hdiff : ∀ (t : ℝ) (y : E), y ∈ S → HasFDerivAt (U t) (fderiv ℝ (U t) y) y := fun t y hy =>
    (fderiv_slice hS hU hy).differentiableAt.hasFDerivAt
  have hcD : Continuous (fun t => fderiv ℝ (U t) x) :=
    hDc.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)
  have hIntD := int_real hg hgc hcD
  have key : HasFDerivAt (fun x' => ∫ t, g t • U t x') (∫ t, g t • fderiv ℝ (U t) x) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x r)
      (F := fun x' t => g t • U t x') (F' := fun x' t => g t • fderiv ℝ (U t) x')
      (bound := fun t => |g t| * C) (Metric.closedBall_mem_nhds x hr) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hS.mem_nhds hx] with y hy
      exact (int_real hg hgc (hsl y hy)).aestronglyMeasurable
    · exact int_real hg hgc (hsl x hx)
    · exact hIntD.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      by_cases ht : t ∈ tsupport g
      · have := hC (t, y) ⟨hT ht, hy⟩
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      · have hz : g t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp [hz]
    · have : Continuous (fun t => |g t| * C) := (continuous_abs.comp hg).mul continuous_const
      refine Continuous.integrable_of_hasCompactSupport this ?_
      exact (hgc.comp_left (g := fun a : ℝ => |a|) (by simp)).mul_right
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      exact (hdiff t y (hball hy)).const_smul (g t)
  rw [key.fderiv, ContinuousLinearMap.integral_apply hIntD]
  rfl

end Gen

theorem contDiff_mulRight (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  have : (fun y : Mat n => y * X) = ((LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap : Mat n → Mat n) := by
    funext y; simp
  rw [this]
  exact ContinuousLinearMap.contDiff _

theorem sm_Rd (X : Mat n) {U : ℝ → Mat n → V} (hU : Sm U) : Sm (fun t => Rd X (U t)) :=
  gen_sm (isOpen_invertible_matrices n) hU (contDiff_mulRight X)

theorem cont_slice {U : ℝ → Mat n → V} (hU : Sm U) {x : Mat n} (hx : x ∈ GLs n) :
    Continuous (fun t => U t x) := by
  have h : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hU.continuousOn
  exact h.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)

theorem bump_support {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |T|) ?_
  intro t ht
  refine hg.2.2 t (lt_of_le_of_lt (le_abs_self T) ?_)
  simpa [Metric.mem_closedBall, Real.dist_eq] using ht

theorem int_sm {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun t => (g t : ℂ) • U t x) := by
  simpa only [Complex.coe_smul] using int_real hg.1.continuous (bump_support hg) (cont_slice hU hx)

theorem rd_avg [CompleteSpace V] (X : Mat n) {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T)
    {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • Rd X (U t) x := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  simp only [Complex.coe_smul]
  exact gen_avg (isOpen_invertible_matrices n) hU hg.1.continuous (bump_support hg) hx (x * X)

def Good (L : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ U : ℝ → Mat n → V, Sm U → Sm (fun t => L (U t))) ∧
  (∀ F F' : Mat n → V, (∀ y ∈ GLs n, F y = F' y) → ∀ x ∈ GLs n, L F x = L F' x) ∧
  ∀ (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), Sm U → IsBump g T → ∀ x ∈ GLs n,
    L (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • L (U t) x

theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ => rfl⟩

theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun U _ => ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩
  exact (contDiffOn_const (c := (0 : V))).congr (fun _ _ => rfl)

theorem good_comp {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ (L₂ f)) := by
  refine ⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun F F' h => h₁.2.1 _ _ (h₂.2.1 F F' h), ?_⟩
  intro U g T hU hg x hx
  show L₁ (L₂ _) x = ∫ t, (g t : ℂ) • L₁ (L₂ (U t)) x
  rw [h₁.2.1 _ (fun x' => ∫ t, (g t : ℂ) • L₂ (U t) x') (h₂.2.2 U g T hU hg) x hx]
  exact h₁.2.2 _ g T (h₂.1 U hU) hg x hx

theorem good_add {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ f + L₂ f) := by
  refine ⟨fun U hU => ?_, fun F F' h x hx => ?_, ?_⟩
  · exact ((h₁.1 U hU).add (h₂.1 U hU)).congr (fun _ _ => rfl)
  · simp only [Pi.add_apply, h₁.2.1 F F' h x hx, h₂.2.1 F F' h x hx]
  · intro U g T hU hg x hx
    simp only [Pi.add_apply, smul_add]
    rw [integral_add (int_sm (h₁.1 U hU) hg hx) (int_sm (h₂.1 U hU) hg hx),
      h₁.2.2 U g T hU hg x hx, h₂.2.2 U g T hU hg x hx]

theorem good_smul (c : ℂ) {L : (Mat n → V) → (Mat n → V)} (h : Good L) : Good (fun f => c • L f) := by
  refine ⟨fun U hU => ?_, fun F F' e x hx => ?_, ?_⟩
  · exact ((h.1 U hU).const_smul c).congr (fun _ _ => rfl)
  · simp only [Pi.smul_apply, h.2.1 F F' e x hx]
  · intro U g T hU hg x hx
    simp only [Pi.smul_apply]
    rw [h.2.2 U g T hU hg x hx, ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => smul_comm _ _ _)

theorem good_sum {ι : Type} (s : Finset ι) {L : ι → (Mat n → V) → (Mat n → V)} (h : ∀ i, Good (L i)) :
    Good (fun f => ∑ i ∈ s, L i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

theorem good_Rd [CompleteSpace V] (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun U hU => sm_Rd X hU, fun F F' h x hx => ?_, fun U g T hU hg x hx => rd_avg X hU hg hx⟩
  have he : F =ᶠ[𝓝 x] F' := Filter.eventuallyEq_of_mem ((isOpen_invertible_matrices n).mem_nhds hx) h
  show fderiv ℝ F x (x * X) = fderiv ℝ F' x (x * X)
  rw [he.fderiv_eq]

theorem good_Eu [CompleteSpace V] (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))

theorem good_Epow [CompleteSpace V] (s : Bool) (m : ℕ) (a b : Fin n) : Good (n := n) (V := V) (Epow s m a b) := by
  induction m generalizing a b with
  | zero =>
    by_cases h : a = b
    · simpa [Epow, h] using good_id
    · simpa [Epow, h] using good_zero
  | succ m ih =>
    exact good_sum Finset.univ fun c => good_comp (good_Eu s a c) (ih c b)

theorem good_gel [CompleteSpace V] (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ fun a => good_Epow s m a a

theorem good_zOp [CompleteSpace V] (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    show Good (fun f => gel p.1 p.2 (zOp w f))
    exact good_comp (good_gel p.1 p.2) ih

theorem zOp_avg : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V)
    (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T →
    ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x :=
  fun _ _ _ _ _ U g T w hU hg x hx => (good_zOp w).2.2 U g T hU hg x hx

end GlobalTheory.CompanionTheory.WaveMult.ZOpAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegralStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_operator_commutes_integral : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T → ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | exact GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoClm
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveField

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_clm_apply {M V : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set M} {B : M → (V →L[ℂ] V)} {f : M → V}
    (hB : ContDiffOn ℝ ∞ B s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x => B x (f x)) s := by
  have hL : ContDiffOn ℝ ∞ (fun x => (B x).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn hB
  exact hL.clm_apply hf

theorem deriv_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {h : ℝ → V} (hh : Differentiable ℝ h) (s : ℝ) :
    deriv (fun r => B (h r)) s = B (deriv h s) :=
  ((B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hh s).hasDerivAt).deriv

theorem iteratedDeriv_two_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    iteratedDeriv 2 (fun s => B (f s)) t = B (iteratedDeriv 2 f t) := by
  have h1 : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (fun s => B (f s)) = fun s => B (deriv f s) := funext (deriv_clm B h1)
  rw [this, deriv_clm B h2, iteratedDeriv_succ, iteratedDeriv_one]

theorem waveA : WaveA := by
  intro hGF n E W₁ W₂ hW A u hA hQ hu hN
  obtain ⟨hs, hce, heq, hd0⟩ := hu
  have hline : ∀ g ∈ GLs n, ContDiff ℝ ∞ (fun s => u s g) := by
    intro g hg
    have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, g)) := contDiff_id.prodMk contDiff_const
    exact contDiffOn_univ.1 (hs.comp hc.contDiffOn fun s _ => ⟨trivial, hg⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => A p.2) (Set.univ ×ˢ GLs n) :=
      hA.1.comp contDiff_snd.contDiffOn fun p hp => hp.2
    exact contDiffOn_clm_apply h1 hs
  · intro t
    refine ⟨contDiffOn_clm_apply hA.1 (hce t).1, fun g hg k => ?_⟩
    show A (g * k.1) (u t (g * k.1)) = E.ρ k⁻¹ (A g (u t g))
    rw [(hce t).2 g hg k, hA.2 g hg k]
    simp only [ContinuousLinearMap.mul_apply]
    have : E.ρ k (E.ρ k⁻¹ (u t g)) = u t g := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul]; simp
    rw [this]
  · intro t g hg
    rw [iteratedDeriv_two_clm (A g) (hline g hg), heq t g hg]
    have hG := fun s => hGF n E.V W₁ W₂ hW A (u t) hA.1 (hce t).1 hQ (hN t) s 2 g hg
    simp only [Om, Pi.smul_apply, Pi.add_apply, hG, map_smul, map_add (f := _)]
  · intro g hg
    rw [deriv_clm (A g) ((hline g hg).differentiable (by simp)), hd0 g hg, map_zero]

end GlobalTheory.CompanionTheory.WaveField
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsWaveTranslateSub
noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveInv

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem gls_mul {h x : Mat n} (hh : h ∈ GLs n) (hx : x ∈ GLs n) : h * x ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hh hx

theorem gls_val (v : G n) : v.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero

theorem contDiff_mulLeft (h : Mat n) : ContDiff ℝ ∞ (fun x : Mat n => h * x) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ h)).contDiff

theorem contDiffOn_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {h : Mat n} (hh : h ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (h * y)) (GLs n) :=
  hf.comp (contDiff_mulLeft h).contDiffOn fun _ hy => gls_mul hh hy

theorem gel_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    gel s m (fun y => f₁ y - f₂ y) g = gel s m f₁ g - gel s m f₂ g := by
  have hP : ContDiffOn ℝ ∞ (fun y => (f₁ y, f₂ y)) (GLs n) := h₁.prodMk h₂
  have c := ((hG n (V × V) V s m (fun y => (f₁ y, f₂ y)) hP).2 g hg).2.2
  have a : gel s m f₁ g = _ := c (ContinuousLinearMap.fst ℂ V V)
  have b : gel s m f₂ g = _ := c (ContinuousLinearMap.snd ℂ V V)
  have d : gel s m (fun y => f₁ y - f₂ y) g = _ :=
    c (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  rw [d, a, b]
  rfl

theorem Om_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => f₁ y - f₂ y) g = Om f₁ g - Om f₂ g := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_sub hG _ _ h₁ h₂ hg]
  module

theorem Om_translate (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {h g : Mat n} (hh : h ∈ GLs n) (hg : g ∈ GLs n) :
    Om (fun y => f (h * y)) g = Om f (h * g) := by
  have c := fun s m => (((hG n V V s m f hf).2 g hg).2.1 h hh).1
  simp only [Om, Pi.smul_apply, Pi.add_apply, c]

theorem contDiff_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {y : Mat n} (hy : y ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s y) := by
  have hl : ContDiff ℝ ∞ (fun s : ℝ => (s, y)) := contDiff_id.prodMk contDiff_const
  have := hu.1.comp hl.contDiffOn (s := Set.univ) fun s _ => ⟨Set.mem_univ _, hy⟩
  exact contDiffOn_univ.mp this

theorem isWave_translate_sub (hG : GelComm) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u)
    {h : Mat n} (hh : h ∈ GLs n) : IsWave E (fun t x => u t (h * x) - u t x) := by
  have hs : ∀ t, ContDiffOn ℝ ∞ (u t) (GLs n) := fun t => (hu.2.1 t).1
  refine ⟨?_, fun t => ⟨(contDiffOn_translate (hs t) hh).sub (hs t), fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · have hmap : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1, h * p.2)) :=
      contDiff_fst.prodMk ((contDiff_mulLeft h).comp contDiff_snd)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Function.uncurry u (p.1, h * p.2)) (Set.univ ×ˢ GLs n) :=
      hu.1.comp hmap.contDiffOn fun p hp => ⟨Set.mem_univ _, gls_mul hh hp.2⟩
    exact h1.sub hu.1
  · have e₁ := (hu.2.1 t).2 (h * g) (gls_mul hh hg) k
    have e₂ := (hu.2.1 t).2 g hg k
    simp only [← mul_assoc, e₁, e₂, map_sub]
  · have hc₁ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s (h * g)) t :=
      (contDiff_infty.mp (contDiff_line hu (gls_mul hh hg)) 2).contDiffAt
    have hc₂ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s g) t :=
      (contDiff_infty.mp (contDiff_line hu hg) 2).contDiffAt
    rw [iteratedDeriv_fun_sub hc₁ hc₂, hu.2.2.1 t _ (gls_mul hh hg), hu.2.2.1 t _ hg,
      Om_sub hG (contDiffOn_translate (hs t) hh) (hs t) hg, Om_translate hG (hs t) hh hg]
  · have d₁ : DifferentiableAt ℝ (fun s => u s (h * g)) 0 :=
      ((contDiff_line hu (gls_mul hh hg)).differentiable (by simp)).differentiableAt
    have d₂ : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((contDiff_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_sub d₁ d₂, hu.2.2.2 _ (gls_mul hh hg), hu.2.2.2 _ hg, sub_zero]

theorem waveN : PositivityTheory.RgBcC.VC.WaveN := by
  intro hEx hSp hG n E W₁ W₂ f hf hN
  obtain ⟨u, hu, h0⟩ := hEx n E f hf
  refine ⟨u, hu, h0, fun t v hv x hx => ?_⟩
  obtain ⟨c, hc⟩ := hSp n
  have hvG := gls_val v
  have hz := hc E _ (isWave_translate_sub hG hu hvG) t x hx fun y hy _ => by
    have hxy := gls_mul hx hy
    rw [h0 _ (gls_mul hvG hxy), h0 _ hxy, hN v hv _ hxy, sub_self]
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.WaveInv
end
end
