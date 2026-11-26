module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemNilSet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ParamInt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_of_iteratedFDeriv_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => F p.1 p.2) =
      fun p => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) W (fun _ => 0)
        (iteratedFDeriv ℝ 0 (F p.1) p.2) := by
    funext p; simp
  rw [e]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

theorem continuousOn_iteratedFDeriv_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W} (m : ℕ)
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) =
      fun p : X × E => continuousMultilinearCurryRightEquiv' ℝ m E W
        (iteratedFDeriv ℝ (m + 1) (F p.1) p.2) := by
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn h

theorem integrable_bound {K : Set X} (hK : IsCompact K) (C : ℝ) :
    Integrable ((toMeasurable ν K).indicator fun _ => C) ν := by
  rw [integrable_indicator_iff (measurableSet_toMeasurable ν K)]
  refine integrableOn_const ?_
  rw [measure_toMeasurable]
  exact hK.measure_lt_top.ne

theorem le_bound {W : Type} [NormedAddCommGroup W] {K : Set X} {C : ℝ} {t : X} {w : W}
    (h1 : t ∈ K → ‖w‖ ≤ C) (h2 : t ∉ K → w = 0) :
    ‖w‖ ≤ (toMeasurable ν K).indicator (fun _ => max C 0) t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem (subset_toMeasurable ν K ht)]
    exact (h1 ht).trans (le_max_left _ _)
  · rw [h2 ht, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem hasFDerivAt_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) {F : X → E → V}
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h0 : ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U))
    (hd : ContinuousOn (fun p : X × E => fderiv ℝ (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0)
    {x₀ : E} (hx : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
  obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
  have hN : U ∩ interior U' ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx) (interior_mem_nhds.2 hU')
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hN
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hKB := hK.prod hBc
  have hsub : K ×ˢ Metric.closedBall x₀ r ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, (hball hp.2).1⟩
  obtain ⟨C, hC⟩ := hKB.exists_bound_of_continuousOn (hd.mono hsub)
  obtain ⟨C₀, hC₀⟩ := hKB.exists_bound_of_continuousOn (h0.mono hsub)
  have hx₀B : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hdz : ∀ t ∉ K, ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ (F t) x = 0 := by
    intro t ht x hxB
    have : F t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_interior.mem_nhds (hball hxB).2] with y hy
      exact hz t ht y (interior_subset hy)
    rw [this.fderiv_eq]
    simp
  have hct : ∀ x ∈ U, Continuous fun t => F t x := fun x hxU =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  have hcd : ∀ x ∈ U, Continuous fun t => fderiv ℝ (F t) x := fun x hxU =>
    hd.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => F t x)
    (F' := fun x t => fderiv ℝ (F t) x) (s := Metric.closedBall x₀ r)
    (bound := (toMeasurable ν K).indicator fun _ => max C 0)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ (integrable_bound hK _) ?_
  · filter_upwards [hU.mem_nhds hx] with x hxU
    exact (hct x hxU).aestronglyMeasurable
  · refine Integrable.mono' (integrable_bound (ν := ν) hK (max C₀ 0))
      (hct x₀ hx).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    exact le_bound (fun ht => hC₀ (t, x₀) ⟨ht, hx₀B⟩) (fun ht => hz t ht x₀ (interior_subset (hball hx₀B).2))
  · exact (hcd x₀ hx).aestronglyMeasurable
  · refine ae_of_all _ fun t x hxB => ?_
    exact le_bound (fun ht => hC (t, x) ⟨ht, hxB⟩) (fun ht => hdz t ht x hxB)
  · refine ae_of_all _ fun t x hxB => ?_
    exact (((h1 t).contDiffAt (hU.mem_nhds (hball hxB).1)).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_integral_nat {U : Set E} (hU : IsOpen U) (m : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : X → E → V),
      (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ContDiffOn ℝ m (fun x => ∫ t, F t x ∂ν) U := by
  have key : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : X → E → V), (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ∀ x₀ ∈ U, HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
    intro V _ _ _ F h1 h2 h3 x₀ hx
    exact hasFDerivAt_integral hU h1 (continuousOn_of_iteratedFDeriv_zero (h2 0))
      (continuousOn_of_iteratedFDeriv_zero (F := fun t => fderiv ℝ (F t))
        (continuousOn_iteratedFDeriv_fderiv 0 (h2 1))) h3 hx
  induction m with
  | zero =>
    intro V _ _ _ F h1 h2 h3
    have : ContinuousOn (fun x => ∫ t, F t x ∂ν) U := fun x hx =>
      (key V F h1 h2 h3 x hx).continuousAt.continuousWithinAt
    have h : ContDiffOn ℝ 0 (fun x => ∫ t, F t x ∂ν) U := contDiffOn_zero.2 this
    simpa using h
  | succ m ih =>
    intro V _ _ _ F h1 h2 h3
    have hG1 : ∀ t, ContDiffOn ℝ ∞ (fderiv ℝ (F t)) U := fun t =>
      (h1 t).fderiv_of_isOpen hU (by simp)
    have hG2 : ∀ k : ℕ, ContinuousOn
        (fun p : X × E => iteratedFDeriv ℝ k (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := fun k =>
      continuousOn_iteratedFDeriv_fderiv k (h2 (k + 1))
    have hG3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧
        ∀ t ∉ K, ∀ x ∈ U', fderiv ℝ (F t) x = 0 := by
      intro x₀ hx
      obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
      refine ⟨interior U', interior_mem_nhds.2 hU', K, hK, fun t ht x hxU => ?_⟩
      have : F t =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
        exact hz t ht y (interior_subset hy)
      rw [this.fderiv_eq]
      simp
    have hI := ih (E →L[ℝ] V) (fun t => fderiv ℝ (F t)) hG1 hG2 hG3
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (key V F h1 h2 h3 x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (key V F h1 h2 h3 x hx).fderiv

theorem contDiffOn_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) (F : X → E → V)
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h2 : ∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) U :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_nat hU m V F h1 h2 h3

theorem intSmooth : PositivityTheory.RgBcC.VC.IntSmooth := by
  intro n X _ _ _ _ ν _ V _ _ _ F h1 h2 h3
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hU : IsOpen (PositivityTheory.RgBcC.GLs n) := by
    have h : Continuous fun g : PositivityTheory.RgTw.Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne_fun h continuous_const
  exact contDiffOn_integral hU F h1 h2 h3

end GlobalTheory.CompanionTheory.ParamInt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerComm
noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace KC

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by
    ext g; rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem mul_val_mem {x : Mat n} (hx : x ∈ GLs n) (y : G n) : x * y.val ∈ GLs n := by
  show (x * y.val).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

section Congr

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (X : Mat n) : EqOn (Rd X f₁) (Rd X f₂) (GLs n) := by
  intro g hg
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (h.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg))]

theorem eu_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f₁) (Eu s a b f₂) (GLs n) := by
  intro g hg
  have h1 := rd_congr h (Matrix.single a b 1) hg
  have h2 := rd_congr h (Matrix.single a b Complex.I) hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2]

theorem epow_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), EqOn (Epow s m a b f₁) (Epow s m a b f₂) (GLs n)
  | 0, a, b => by
    intro g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | m + 1, a, b => by
    intro g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (epow_congr h s m c b) s a c hg

theorem gel_congr {f₁ f₂ : Mat n → V} (h : EqOn f₁ f₂ (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f₁) (gel s m f₂) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem zop_congr : ∀ (w : List (Bool × ℕ)) {f₁ f₂ : Mat n → V}, EqOn f₁ f₂ (GLs n) →
    EqOn (zOp w f₁) (zOp w f₂) (GLs n)
  | [], _, _, h => h
  | p :: w, _, _, h => by
    intro g hg
    exact gel_congr (zop_congr w h) p.1 p.2 hg

end Congr

section Props

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem gel_ninv (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {F : Mat n → V}
    (hF : ContDiffOn ℝ ∞ F (GLs n)) (hN : NInv W₁ W₂ F) (s : Bool) (m : ℕ) : NInv W₁ W₂ (gel s m F) := by
  intro u hu x hx
  have h1 := ((hGC n V V s m F hF).2 x hx).2.1 u.val (val_mem u)
  rw [← h1.1]
  exact gel_congr (fun y hy => hN u hu y hy) s m hx

theorem zop_props (hGC : GelComm) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      ContDiffOn ℝ ∞ (zOp w F) (GLs n) ∧ NInv W₁ W₂ (zOp w F) := by
  intro w
  induction w with
  | nil => exact fun F hF hN => ⟨hF, hN⟩
  | cons p w ih =>
    intro F hF hN
    obtain ⟨h1, h2⟩ := ih F hF hN
    exact ⟨(hGC n V V p.1 p.2 _ h1).1, gel_ninv hGC h1 h2 p.1 p.2⟩

theorem zop_field (hGC : GelComm) (hGF : GelFlag) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (A : Mat n → (V →L[ℂ] V)) (hA : ContDiffOn ℝ ∞ A (GLs n)) (hQ : QInv W₁ W₂ A) :
    ∀ (w : List (Bool × ℕ)) (F : Mat n → V), ContDiffOn ℝ ∞ F (GLs n) → NInv W₁ W₂ F →
      EqOn (zOp w (fun y => A y (F y))) (fun y => A y (zOp w F y)) (GLs n) := by
  intro w
  induction w with
  | nil => exact fun _ _ _ _ _ => rfl
  | cons p w ih =>
    intro F hF hN x hx
    obtain ⟨h1, h2⟩ := zop_props hGC w F hF hN
    show gel p.1 p.2 (zOp w (fun y => A y (F y))) x = A x (gel p.1 p.2 (zOp w F) x)
    rw [gel_congr (ih F hF hN) p.1 p.2 hx]
    exact hGF n V W₁ W₂ hW A (zOp w F) hA h1 hQ h2 p.1 p.2 x hx

end Props

section Slice

variable {P Q W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slice_eq {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (p : P) :
    ∀ m : ℕ, ∀ x ∈ O, iteratedFDeriv ℝ m (fun y => U (p, y)) x =
      (iteratedFDeriv ℝ m U (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q) := by
  intro m
  induction m with
  | zero =>
    intro x _
    ext h
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro x hx
    have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
    have hpx : (p, x) ∈ (Set.univ ×ˢ O : Set (P × Q)) := ⟨trivial, hx⟩
    have hev : (iteratedFDeriv ℝ m (fun y => U (p, y))) =ᶠ[nhds x]
        (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) :=
      Filter.eventually_of_mem (hO.mem_nhds hx) fun y hy => ih y hy
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m U) (p, x) := by
      have h1 := hU.differentiableOn_iteratedFDerivWithin (m := m) (by exact_mod_cast ENat.natCast_lt_top m) hS.uniqueDiffOn
      have h2 : DifferentiableOn ℝ (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
        h1.congr fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
      exact h2.differentiableAt (hS.mem_nhds hpx)
    have hj : HasFDerivAt (fun y : Q => (p, y)) (ContinuousLinearMap.inr ℝ P Q) x := hasFDerivAt_prodMk_right p x
    have hC : HasFDerivAt (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q))
        (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) (iteratedFDeriv ℝ m U (p, x)) :=
      ContinuousLinearMap.hasFDerivAt _
    have hcomp := hC.comp x (hdiff.hasFDerivAt.comp x hj)
    have hfun : (fun y => (iteratedFDeriv ℝ m U (p, y)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P Q)) =
        ⇑(ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)) ∘ iteratedFDeriv ℝ m U ∘ Prod.mk p := by
      funext y; rfl
    ext h
    rw [iteratedFDeriv_succ_apply_left, hev.fderiv_eq, hfun, hcomp.fderiv]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    rw [iteratedFDeriv_succ_apply_left]
    rfl

theorem slice_cont {U : P × Q → W} {O : Set Q} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U (Set.univ ×ˢ O)) (m : ℕ) :
    ContinuousOn (fun q : P × Q => iteratedFDeriv ℝ m (fun y => U (q.1, y)) q.2) (Set.univ ×ˢ O) := by
  have hS : IsOpen (Set.univ ×ˢ O : Set (P × Q)) := isOpen_univ.prod hO
  have h1 : ContinuousOn (iteratedFDeriv ℝ m U) (Set.univ ×ˢ O) :=
    (hU.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top) hS.uniqueDiffOn).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen m hS hy).symm
  have h2 := ((ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := W)
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ P Q)).continuous.comp_continuousOn h1)
  refine h2.congr fun q hq => ?_
  have := slice_eq hO hU q.1 m q.2 hq.2
  simp only [Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  rw [this]

end Slice

end KC

open KC in
theorem kerComm_of (hWN : WaveN) (hWA : WaveA) : KerComm := by
  intro hWE hWS hGC hGF hIS n _ _ μ _ E w g T k hg hk W₁ W₂ hW A hA hQ f hf hfN x hx
  obtain ⟨u, hu, hu0, huN⟩ := hWN hWE hWS hGC n E W₁ W₂ f hf hfN
  have hv := hWA hGF n E W₁ W₂ hW A u hA hQ hu huN
  have h1 := hk.2.2.2 _ hv x hx
  have h2 := hk.2.2.2 _ hu x hx

  have hS : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) := isOpen_univ.prod isOpen_GLs
  have hgc : ContDiff ℝ ∞ fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
  have hU' : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((g p.1 : ℝ) : ℂ) • u p.1 p.2) (Set.univ ×ˢ GLs n) :=
    hgc.contDiffOn.smul hu.1
  have hFs : ContDiffOn ℝ ∞ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') (GLs n) := by
    refine hIS n ℝ MeasureTheory.volume E.V (fun t x' => ((g t : ℝ) : ℂ) • u t x') ?_ ?_ ?_
    · intro t
      exact hU'.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) fun y hy => ⟨trivial, hy⟩
    · intro m
      exact slice_cont isOpen_GLs hU' m
    · intro x₀ _
      refine ⟨Set.univ, Filter.univ_mem, Set.Icc (-T) T, isCompact_Icc, fun t ht y _ => ?_⟩
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hFN : NInv W₁ W₂ (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') := by
    intro v hv' y hy
    simp only
    congr 1
    funext t
    rw [huN t v hv' y hy]
  have hint : ∀ x' ∈ GLs n, Integrable (fun t => ((g t : ℝ) : ℂ) • u t x') := by
    intro x' hx'
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := hU'.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨trivial, hx'⟩
      exact this
    · refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc fun t ht => ?_
      have : T < |t| := by
        by_contra hc
        exact ht ⟨by linarith [neg_abs_le t, not_lt.1 hc], le_trans (le_abs_self t) (not_lt.1 hc)⟩
      simp [hg.2.2 t this]
  have hcong : EqOn (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x'))
      (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) (GLs n) := by
    intro x' hx'
    simp only
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint x' hx')]
    congr 1
    funext t
    rw [map_smul]
  calc act μ E k (fun y => A y (f y)) x = act μ E k (fun y => A y (u 0 y)) x := by
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]
    _ = zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • A x' (u t x')) x := h1
    _ = zOp w (fun x' => A x' (∫ t, ((g t : ℝ) : ℂ) • u t x')) x := zop_congr w hcong hx
    _ = A x (zOp w (fun x' => ∫ t, ((g t : ℝ) : ℂ) • u t x') x) :=
        zop_field hGC hGF hW A hA.1 hQ w _ hFs hFN hx
    _ = A x (act μ E k (u 0) x) := by rw [h2]
    _ = A x (act μ E k f x) := by
        congr 1
        simp only [act]
        congr 1
        funext y
        rw [hu0 _ (mul_val_mem hx y)]

end PositivityTheory.RgBcC.VC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  show k.1.det ≠ 0
  intro h0
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

def trT {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : V →L[ℂ] V) :
    (V →L[ℂ] V) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ V).comp ((ContinuousLinearMap.coeLM ℂ).comp ((ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip T).toLinearMap))

theorem trT_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T B : V →L[ℂ] V) :
    trT T B = LinearMap.trace ℂ V ((B * T : V →L[ℂ] V) : V →ₗ[ℂ] V) := rfl

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  show (1 : Mat n).det ≠ 0
  simp

theorem vcKer_of (hKC : KerComm) (hKN : KerNId) (hNA : NAvg) (hTZ : TrZero) (hLg : LgCpt) : VCKer := by
  intro hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h _ _ μ _ w g τ k hg hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _
  obtain ⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩ := hFF n W₁ W₂ hW hW1
  let A : Mat n → (E.V →L[ℂ] E.V) := fun x => ε (H x)
  have hA : IsField E A := by
    refine ⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, fun x hx k₀ => ?_⟩
    have e1 := h.frε k₀.1 (unitary_mem_GLs k₀) (H x) (hHh x hx)
    rw [h.onK k₀] at e1
    have e2 : E.ρ k₀⁻¹ * E.ρ k₀ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    show ε (H (x * k₀.1)) = E.ρ k₀⁻¹ * ε (H x) * E.ρ k₀
    rw [hHk x hx k₀]
    calc ε (k₀.1ᴴ * H x * k₀.1) = (E.ρ k₀⁻¹ * E.ρ k₀) * ε (k₀.1ᴴ * H x * k₀.1) := by rw [e2, one_mul]
      _ = E.ρ k₀⁻¹ * (E.ρ k₀ * ε (k₀.1ᴴ * H x * k₀.1)) := mul_assoc _ _ _
      _ = E.ρ k₀⁻¹ * (ε (H x) * E.ρ k₀) := by rw [← e1]
      _ = E.ρ k₀⁻¹ * ε (H x) * E.ρ k₀ := (mul_assoc _ _ _).symm
  have hAq : QInv W₁ W₂ A := fun q hq h1 h2 x hx => by
    show ε (H (q * x)) = ε (H x)
    rw [hHq q hq h1 h2 x hx]
  have hcomm := hKC hWE hWS hGC hGF hIS n μ E w g τ k hg hk W₁ W₂ hW A hA hAq
  obtain ⟨hks, ⟨R, hR⟩, hbi, -⟩ := hk
  have hid := hKN hNU hKZ hNA n μ E k hks ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hAq hcomm d.val (mem_GLs d)
  have hd : A d.val = -A 1 := by
    show ε (H d.val) = -ε (H 1)
    rw [hHd d.val (mem_GLs d) hd1 hd2, map_neg]
  rw [hd] at hid
  set B := ∫ u : N, k ((u : G n).val * d.val) ∂ν with hBdef
  have hanti : A 1 * B = -(B * A 1) := by rw [← hid, mul_neg]
  have htr : trT T B = 0 := by
    rw [trT_apply]
    exact hTZ E.V B T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr
      (h.car _ _ (hHh 1 one_mem_GLs) (hHh 1 one_mem_GLs)) hanti (h.Tε _)
  have hcont : Continuous fun u : N => k ((u : G n).val * d.val) := by
    refine hks.continuousOn.comp_continuous ?_ fun u => ?_
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_mul continuous_const
    · exact mem_GLs ((u : G n) * d)
  have hNc : IsClosed (N : Set (G n)) := (hNU n W₁ W₂ hW N hN).1
  have hK : IsCompact ((fun u : N => (u : G n)) ⁻¹' ((fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R})) := by
    refine hNc.isClosedEmbedding_subtypeVal.isCompact_preimage ?_
    have : (fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R} = (fun y : G n => y * d⁻¹) '' {y : G n | lg y.val ≤ R} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy
        exact ⟨y * d, hy, by rw [mul_assoc, mul_inv_cancel, mul_one]⟩
      · rintro ⟨z, hz, rfl⟩
        rwa [Set.mem_ofPred_eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact (hLg n R).image (continuous_id.mul continuous_const)
  have hcpt : HasCompactSupport fun u : N => k ((u : G n).val * d.val) := by
    refine HasCompactSupport.intro hK fun u hu => ?_
    refine hR _ (mem_GLs ((u : G n) * d)) ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hu
    exact hu
  have hint : Integrable (fun u : N => k ((u : G n).val * d.val)) ν := hcont.integrable_of_hasCompactSupport hcpt
  have hphi : (fun u : N => phiOf E T k (u * d)) = fun u : N => trT T (k ((u : G n).val * d.val)) := rfl
  refine ⟨by rw [hphi]; exact (trT T).integrable_comp hint, ?_⟩
  rw [hphi, (trT T).integral_comp_comm hint]
  exact htr

theorem vcOf_of (hIS : IntSmooth) (hVK : VCKer) : VCOf := by
  intro hWE hWS _ hGC hGF hFF hNU hKZ n lam E Fr ε ι S Γ T h _ _ μ _ k val τ hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hk
  have key : ∀ i, Integrable (fun u : N => phiOf E T (ks i) (u * d)) ν ∧ ∫ u : N, phiOf E T (ks i) (u * d) ∂ν = 0 :=
    fun i => hVK hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h μ (w i) (g i) τ (ks i) (hks i).1 (hks i).2
      d W₁ W₂ hW hW1 hd1 hd2 N hN ν
  have hpt : (fun u : N => phiOf E T k (u * d)) = fun u : N => ∑ i, c i * phiOf E T (ks i) (u * d) := by
    funext u
    show trT T (k ((u : G n) * d).val) = ∑ i, c i * trT T (ks i ((u : G n) * d).val)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum _ (mem_GLs _), map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hpt, integral_finsetSum _ fun i _ => (key i).1.const_mul (c i)]
  simp only [integral_const_mul, (key _).2, mul_zero, Finset.sum_const_zero]

end PositivityTheory.RgBcC.VC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.TrZero
noncomputable section

namespace PositivityTheory.RgBcC.VC

theorem trZero : TrZero := by
  intro V _ _ _ B T e i c hc hei heB hTe
  let t : (V →L[ℂ] V) → ℂ := fun A => LinearMap.trace ℂ V (A : V →ₗ[ℂ] V)
  have tadd : ∀ A A' : V →L[ℂ] V, t (A + A') = t A + t A' := fun A A' => by
    simp only [t, ContinuousLinearMap.coe_add, map_add (f := _)]
  have tneg : ∀ A : V →L[ℂ] V, t (-A) = -t A := fun A => by
    simp only [t, ContinuousLinearMap.coe_neg, map_neg]
  have tsmul : ∀ (a : ℂ) (A : V →L[ℂ] V), t (a • A) = a * t A := fun a A => by
    simp only [t, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
  have tcomm : ∀ A A' : V →L[ℂ] V, t (A * A') = t (A' * A) := fun A A' =>
    LinearMap.trace_mul_comm ℂ (A : V →ₗ[ℂ] V) (A' : V →ₗ[ℂ] V)
  set X := B * T with hXdef
  have hX : e * X = -(X * e) := by
    calc e * X = (e * B) * T := (mul_assoc _ _ _).symm
      _ = -(B * e) * T := by rw [heB]
      _ = -(B * (e * T)) := by rw [neg_mul, mul_assoc]
      _ = -(B * (T * e)) := by rw [hTe]
      _ = -(X * e) := by rw [hXdef, mul_assoc]
  have h1 : X * (e * i + i * e) = c • X := by rw [hei, mul_smul_comm, mul_one]
  have key : c * t X = 0 := by
    rw [← tsmul, ← h1, mul_add, tadd, ← mul_assoc, ← mul_assoc, tcomm (X * i) e, ← mul_assoc, hX,
      neg_mul, tneg, add_neg_cancel]
  exact (mul_eq_zero.mp key).resolve_left hc

end PositivityTheory.RgBcC.VC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.SecondCountableG
noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC.NAvgH

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def sq (A : Mat n) : ℝ := ∑ a, ∑ b, ‖A a b‖ ^ 2

theorem sq_nonneg' (A : Mat n) : 0 ≤ sq A := by
  unfold sq; positivity

theorem sq_mul_le (A B : Mat n) : sq (A * B) ≤ sq A * sq B := by
  unfold sq
  have h1 : ∀ a b, ‖(A * B) a b‖ ^ 2 ≤ (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
    intro a b
    rw [Matrix.mul_apply]
    calc ‖∑ c, A a c * B c b‖ ^ 2 ≤ (∑ c, ‖A a c‖ * ‖B c b‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul, le_refl]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ a, ∑ b, ‖(A * B) a b‖ ^ 2 ≤ ∑ a, ∑ b, (∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2 := by
        gcongr with a _ b _
        exact h1 a b
    _ = (∑ a, ∑ c, ‖A a c‖ ^ 2) * ∑ c, ∑ b, ‖B c b‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem lg_eq (y : Mat n) : lg y = Real.log (1 + sq y + sq y⁻¹) := by
  simp only [lg, sq, Finset.sum_add_distrib, add_assoc]

theorem lg_mul_le (A B : Mat n) : lg (A * B) ≤ lg A + lg B := by
  rw [lg_eq, lg_eq, lg_eq, Matrix.mul_inv_rev]
  have hA := sq_nonneg' A; have hA' := sq_nonneg' A⁻¹; have hB := sq_nonneg' B; have hB' := sq_nonneg' B⁻¹
  have hxA : 0 < 1 + sq A + sq A⁻¹ := by linarith
  have hxB : 0 < 1 + sq B + sq B⁻¹ := by linarith
  have hxAB : 0 < 1 + sq (A * B) + sq (B⁻¹ * A⁻¹) := by
    have := sq_nonneg' (A * B); have := sq_nonneg' (B⁻¹ * A⁻¹); linarith
  rw [← Real.log_mul hxA.ne' hxB.ne']
  apply Real.log_le_log hxAB
  have e1 := sq_mul_le A B
  have e2 := sq_mul_le B⁻¹ A⁻¹
  nlinarith [mul_nonneg hA hB, mul_nonneg hA' hB', mul_nonneg hA hB', mul_nonneg hA' hB]

theorem lg_inv (A : Mat n) (hA : A ∈ GLs n) : lg A⁻¹ = lg A := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  rw [lg_eq, lg_eq, Matrix.nonsing_inv_nonsing_inv A hA', add_right_comm]

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | det g ≠ 0}
  exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem continuousAt_lg (x : Mat n) (hx : x ∈ GLs n) : ContinuousAt lg x := by
  have hinv : ContinuousAt (fun y : Mat n => y⁻¹) x := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx
  have hsq : Continuous (sq : Mat n → ℝ) := by
    unfold sq
    refine continuous_finsetSum _ (fun a _ => continuous_finsetSum _ (fun b _ => ?_))
    exact (((continuous_apply b).comp (continuous_apply a)).norm).pow 2
  have hpos : 0 < 1 + sq x + sq x⁻¹ := by linarith [sq_nonneg' x, sq_nonneg' x⁻¹]
  rw [show (lg : Mat n → ℝ) = fun y => Real.log (1 + sq y + sq y⁻¹) from funext lg_eq]
  exact ((continuousAt_const.add hsq.continuousAt).add (hsq.continuousAt.comp hinv)).log hpos.ne'

theorem mem_GLsG (y : G n) : y.val ∈ GLs n := by
  show det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem mem_GLs_mul {A B : Mat n} (hA : A ∈ GLs n) (hB : B ∈ GLs n) : A * B ∈ GLs n := by
  show (A * B).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hA hB

def lmulL : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap
        { toFun := fun x => M * x
          map_add' := fun x y => Matrix.mul_add M x y
          map_smul' := fun c x => Matrix.mul_smul M c x }
      map_add' := fun M M' => by ext x : 1; simp [Matrix.add_mul]
      map_smul' := fun c M => by ext x : 1; simp [Matrix.smul_mul] }

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end PositivityTheory.RgBcC.VC.NAvgH

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC.NAvgH
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nAvg_of (hIS : IntSmooth) (hLg : LgCpt) (hNU : NilUni) : NAvg := by
  intro n _ _ E W₁ W₂ hW N hN ν _ φ hφ hφR
  obtain ⟨R, hR⟩ := hφR
  obtain ⟨hNc, hinv⟩ := hNU n W₁ W₂ hW N hN
  haveI := hinv ν
  haveI : SecondCountableTopology (G n) := secondCountable_G
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨hφs, hφk⟩ := hφ
  have hφc : ContinuousOn φ (GLs n) := hφs.continuousOn
  have hmem : ∀ u : N, ∀ x ∈ GLs n, ((u : G n) : Mat n) * x ∈ GLs n :=
    fun u x hx => mem_GLs_mul (mem_GLsG _) hx
  have hlgu : ∀ u x : Mat n, x ∈ GLs n → lg u ≤ lg (u * x) + lg x := by
    intro u x hx
    have h := lg_mul_le (u * x) x⁻¹
    rwa [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hx), lg_inv x hx] at h
  have cpt : ∀ c : ℝ, IsCompact {u : N | lg ((u : G n) : Mat n) ≤ c} := fun c =>
    hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n c)
  have hsupp : ∀ x₀ ∈ GLs n, ∃ U ∈ 𝓝 x₀, ∃ K : Set N, IsCompact K ∧
      ∀ u ∉ K, ∀ x ∈ U, φ (((u : G n) : Mat n) * x) = 0 := by
    intro x₀ hx₀
    refine ⟨GLs n ∩ lg ⁻¹' Set.Iio (lg x₀ + 1),
      Filter.inter_mem (isOpen_GLs.mem_nhds hx₀)
        ((continuousAt_lg x₀ hx₀).preimage_mem_nhds (Iio_mem_nhds (by linarith))),
      _, cpt (R + lg x₀ + 1), ?_⟩
    intro u hu x hx
    have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + lg x₀ + 1 := hu
    have h1 := hlgu ((u : G n) : Mat n) x hx.1
    have h2 : lg x < lg x₀ + 1 := hx.2
    exact hR _ (hmem u x hx.1) (by linarith [lt_of_not_ge hu'])
  have hint : ∀ x ∈ GLs n, Integrable (fun u : N => φ (((u : G n) : Mat n) * x)) ν := by
    intro x hx
    obtain ⟨U, hU, K, hK, hKz⟩ := hsupp x hx
    have hc : Continuous (fun u : N => φ (((u : G n) : Mat n) * x)) :=
      hφc.comp_continuous (by fun_prop) (fun u => hmem u x hx)
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (fun u hu => hKz u hu x (mem_of_mem_nhds hU)))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hmaps : ∀ U : Mat n, U ∈ GLs n → Set.MapsTo (lmulL U) (GLs n) (GLs n) :=
      fun U hU x hx => mem_GLs_mul hU hx
    have hle : ∀ m : ℕ, ((m : ℕ∞ω) ≤ ∞) := fun m => by exact_mod_cast le_top
    have hD : ∀ m : ℕ, ContinuousOn (iteratedFDeriv ℝ m φ) (GLs n) := fun m =>
      (hφs.continuousOn_iteratedFDerivWithin (hle m) isOpen_GLs.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen m isOpen_GLs hx).symm)
    have hform : ∀ (m : ℕ) (U : Mat n), U ∈ GLs n → ∀ x ∈ GLs n,
        iteratedFDeriv ℝ m (φ ∘ ⇑(lmulL U)) x =
          (iteratedFDeriv ℝ m φ (lmulL U x)).compContinuousLinearMap (fun _ => lmulL U) := by
      intro m U hU x hx
      have hopen : IsOpen (⇑(lmulL U) ⁻¹' GLs n) := isOpen_GLs.preimage (lmulL U).continuous
      have hgx : lmulL U x ∈ GLs n := hmaps U hU hx
      have hx' : x ∈ ⇑(lmulL U) ⁻¹' GLs n := hgx
      have h1 := (lmulL U).iteratedFDerivWithin_comp_right hφs isOpen_GLs.uniqueDiffOn
        hopen.uniqueDiffOn hgx (hle m)
      have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ ∘ ⇑(lmulL U)) m hopen hx'
      have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := φ) m isOpen_GLs hgx
      rw [← e1, ← e2]
      exact h1
    have hUc : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n)) := by fun_prop
    have hUx : Continuous (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) := by fun_prop
    have key := hIS n N ν E.V (fun u => φ ∘ ⇑(lmulL ((u : G n) : Mat n)))
      (fun u => hφs.comp (lmulL ((u : G n) : Mat n)).contDiff.contDiffOn (hmaps _ (mem_GLsG _)))
      (fun m => by
        let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin m => Mat n) (fun _ : Fin m => Mat n) E.V
        have hC : Continuous (fun p : N × Mat n => C (fun _ => lmulL ((p.1 : G n) : Mat n))) :=
          C.cont.comp (continuous_pi fun _ => lmulL.continuous.comp hUc)
        have hDp : ContinuousOn
            (fun p : N × Mat n => iteratedFDeriv ℝ m φ (lmulL ((p.1 : G n) : Mat n) p.2))
            (Set.univ ×ˢ GLs n) :=
          (hD m).comp hUx.continuousOn (fun p hp => hmem p.1 p.2 hp.2)
        refine (hC.continuousOn.clm_apply hDp).congr (fun p hp => ?_)
        exact (hform m _ (mem_GLsG _) p.2 hp.2).trans rfl)
      hsupp
    exact key
  · intro g hg k
    have e : ∀ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) = E.ρ k⁻¹ (φ (((u : G n) : Mat n) * g)) := by
      intro u
      rw [← Matrix.mul_assoc]
      exact hφk _ (hmem u g hg) k
    show ∫ u : N, φ (((u : G n) : Mat n) * (g * ↑k)) ∂ν = E.ρ k⁻¹ (∫ u : N, φ (((u : G n) : Mat n) * g) ∂ν)
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact ContinuousLinearMap.integral_comp_comm _ (hint g hg)
  · intro u₀ hu₀ x hx
    have hu₁ : u₀ ∈ N := by
      rw [← SetLike.mem_coe, hN]
      exact hu₀
    set u₁ : N := ⟨u₀, hu₁⟩ with hu₁def
    have key : ∀ f : N → E.V, ∫ u, f (u * u₁) ∂ν = ∫ u, f u ∂ν := by
      intro f
      rw [← integral_inv_eq_self (fun u => f (u * u₁)) ν]
      have hre : ∀ u : N, f (u⁻¹ * u₁) = (fun v => f v⁻¹) (u₁⁻¹ * u) := fun u => by
        simp [_root_.mul_inv_rev]
      simp_rw [hre]
      rw [integral_mul_left_eq_self (fun v => f v⁻¹) u₁⁻¹, integral_inv_eq_self f ν]
    show ∫ u : N, φ (((u : G n) : Mat n) * ((u₀ : Mat n) * x)) ∂ν = ∫ u : N, φ (((u : G n) : Mat n) * x) ∂ν
    rw [← key (fun u => φ (((u : G n) : Mat n) * x))]
    congr 1
    ext u
    simp [hu₁def, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

end PositivityTheory.RgBcC.VC
end
end

namespace PositivityTheory.RgBcC.VC

theorem vcOf : PositivityTheory.RgBcC.VCOf := by
  intro hWE hWS hMA hGC hGF hFF hNU hKZ
  have hKC : KerComm := kerComm_of GlobalTheory.CompanionTheory.WaveInv.waveN GlobalTheory.CompanionTheory.WaveField.waveA
  have hKN : KerNId := kerNId_of' GlobalTheory.CompanionTheory.LgBound.lgCpt
  have hNA : NAvg := nAvg_of GlobalTheory.CompanionTheory.ParamInt.intSmooth GlobalTheory.CompanionTheory.LgBound.lgCpt hNU
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ k val τ hMult d W₁ W₂ hW hW1 hd2 hd1 N hN ν _
  letI : NormedAddCommGroup (RgTw.Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (RgTw.Mat n) := Matrix.normedSpace
  obtain ⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩ := hFF n W₁ W₂ hW hW1
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := hMult
  have hcl : IsClosed (N : Set (RgTw.G n)) := by
    rw [hN]
    have hc : ∀ v : Fin n → ℂ, Continuous (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) := fun v =>
      (Units.continuous_val.sub continuous_const).matrix_mulVec continuous_const
    have e : nilSet W₁ W₂ = (⋂ v, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₂ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₂, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₁ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₁, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' {0}) := by
      ext u
      simp only [nilSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Set.mem_singleton_iff, and_assoc]
    rw [e]
    refine ((isClosed_iInter fun v => W₂.closed_of_finiteDimensional.preimage (hc v)).inter
      (isClosed_biInter fun v _ => W₁.closed_of_finiteDimensional.preimage (hc v))).inter
      (isClosed_biInter fun v _ => isClosed_singleton.preimage (hc v))
  let A : RgTw.Mat n → E.V →L[ℂ] E.V := fun x => ε (H x)
  have hA : IsField E A := by
    refine ⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, ?_⟩
    intro x hx k0
    have hkG : ((k0 : Matrix (Fin n) (Fin n) ℂ) : RgTw.Mat n) ∈ GLs n := by
      have hu := Matrix.det_of_mem_unitary k0.2
      exact right_ne_zero_of_mul_eq_one hu.1
    have h := hCx.frε _ hkG (H x) (hHh x hx)
    rw [hCx.onK] at h
    show ε (H (x * k0)) = E.ρ k0⁻¹ * ε (H x) * E.ρ k0
    rw [hHk x hx k0, mul_assoc (E.ρ k0⁻¹), h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hQ : QInv W₁ W₂ A := by
    intro q hq h1 h2 x hx
    simp only [A, hHq q hq h1 h2 x hx]
  have hdG : (d : RgTw.Mat n) ∈ GLs n := mem_GLs d
  have hAd : A d = -A 1 := by
    simp only [A, hHd _ hdG hd2 hd1, map_neg]
  have hone : ∀ i, MeasureTheory.Integrable (fun u : N => trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n)))) ν ∧
      ∫ u : N, trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ∂ν = 0 := by
    intro i
    obtain ⟨hb, hker⟩ := hks i
    obtain ⟨hsm, ⟨R, hR⟩, hbi, -⟩ := hker
    have hI : MeasureTheory.Integrable (fun u : N => ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ν :=
      KN.integrable_N GlobalTheory.CompanionTheory.LgBound.lgCpt hcl ν (ks i) hsm.continuousOn R hR _ hdG
    refine ⟨(trT T).integrable_comp hI, ?_⟩
    rw [ContinuousLinearMap.integral_comp_comm _ hI]
    have hcomm := hKC hWE hWS hGC hGF GlobalTheory.CompanionTheory.ParamInt.intSmooth n μ E (w i) (g i) τ (ks i) hb (hks i).2
      W₁ W₂ hW A hA hQ
    have key := hKN hNU hKZ hNA n μ E (ks i) hsm ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hQ hcomm _ hdG
    rw [hAd] at key
    have h1G : (1 : RgTw.Mat n) ∈ GLs n := one_mem_GLs
    rw [trT_apply]
    refine trZero E.V _ T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr
      (hCx.car _ _ (hHh 1 h1G) (hHh 1 h1G)) ?_ (hCx.Tε _)
    have : ∀ B : E.V →L[ℂ] E.V, B * -ε (H 1) = -(B * ε (H 1)) := fun B => by rw [mul_neg]
    rw [this] at key
    exact key.symm
  have hsum : ∀ u : N, phiOf E T k ((u : RgTw.G n) * d) =
      ∑ i, c i * trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) := by
    intro u
    have hm : (((u : RgTw.G n) * d : RgTw.G n) : RgTw.Mat n) ∈ GLs n := mem_GLs _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [phiOf, ← trT_apply, hk _ hm, map_sum]
    simp only [map_smul, smul_eq_mul, Units.val_mul]
  simp only [hsum]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hone i).1.const_mul (c i))]
  simp [MeasureTheory.integral_const_mul, (hone _).2]

end PositivityTheory.RgBcC.VC
