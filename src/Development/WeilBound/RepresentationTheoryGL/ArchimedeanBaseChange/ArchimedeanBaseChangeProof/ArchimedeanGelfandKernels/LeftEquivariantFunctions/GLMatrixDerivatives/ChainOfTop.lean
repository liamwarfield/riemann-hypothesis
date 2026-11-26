module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ChainOf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfKer
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.MulMemGLs
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfDC
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfGam
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfLoc
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfEq
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Eq

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_equiv (A : V ≃L[ℂ] V) (X : Mat n) (f : Mat n → V) : Rd X (fun x => A (f x)) = fun x => A (Rd X f x) := by
  funext g
  show fderiv ℝ (fun x => A (f x)) g (g * X) = A (fderiv ℝ f g (g * X))
  by_cases hf : DifferentiableAt ℝ f g
  · have h : HasFDerivAt (fun x => A (f x)) ((A.restrictScalars ℝ : V →L[ℝ] V).comp (fderiv ℝ f g)) g :=
      (A.restrictScalars ℝ : V →L[ℝ] V).hasFDerivAt.comp g hf.hasFDerivAt
    rw [h.fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (fun x => A (f x)) g := by
      intro h
      apply hf
      have h2 : DifferentiableAt ℝ (fun x => A.symm (A (f x))) g :=
        (A.symm.restrictScalars ℝ : V →L[ℝ] V).differentiableAt.comp g h
      simpa using h2
    rw [fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hf]
    simp

theorem eu_equiv (A : V ≃L[ℂ] V) (s : Bool) (a b : Fin n) (f : Mat n → V) :
    Eu s a b (fun x => A (f x)) = fun x => A (Eu s a b f x) := by
  unfold Eu
  rw [rd_equiv, rd_equiv]
  funext x
  by_cases hs : s = true <;> simp [hs, map_add (f := _), map_smul]

theorem epow_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) (f : Mat n → V),
    Epow s m a b (fun x => A (f x)) = fun x => A (Epow s m a b f x) := by
  induction m with
  | zero =>
    intro a b f
    rw [Epow.eq_1]
    funext x
    split_ifs <;> simp
  | succ m ih =>
    intro a b f
    rw [Epow.eq_2]
    simp only [ih, eu_equiv]
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum]

theorem gel_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) (f : Mat n → V) :
    gel s m (fun x => A (f x)) = fun x => A (gel s m f x) := by
  unfold gel
  simp only [epow_equiv]
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finset.sum_apply, map_sum]

theorem om_equiv (A : V ≃L[ℂ] V) (f : Mat n → V) : Om (fun x => A (f x)) = fun x => A (Om f x) := by
  unfold Om
  rw [gel_equiv, gel_equiv]
  funext x
  simp [map_add (f := _), map_nsmul]

theorem zop_equiv (A : V ≃L[ℂ] V) : ∀ (w : List (Bool × ℕ)) (f : Mat n → V),
    zOp w (fun x => A (f x)) = fun x => A (zOp w f x) := by
  intro w
  induction w with
  | nil =>
    intro f
    simp [zOp.eq_1]
  | cons p w ih =>
    intro f
    rw [zOp.eq_2]
    simp only [ih, gel_equiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Eq
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Loc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') U := by
  intro x hx
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') U := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h _ hx, rd_congr hU h _ hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (Epow s m a b f) (Epow s m a b f') U := by
  induction m with
  | zero =>
    intro a b f f' h x hx
    simp only [Epow]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro a b f f' h x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (ih c b h) s a c hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') U := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx

theorem zop_congr {U : Set (Mat n)} (hU : IsOpen U) : ∀ (w : List (Bool × ℕ)) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (zOp w f) (zOp w f') U := by
  intro w
  induction w with
  | nil => intro f f' h; exact h
  | cons p w ih => intro f f' h; exact gel_congr hU (ih h) p.1 p.2

theorem integrable_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (hF : ContinuousOn F (GLs n))
    (hc : Cpt F) : Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val := by
    refine hF.comp_continuous (Units.continuous_val) fun y => ?_
    show (y.val).det ≠ 0
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
  have hlg : ContinuousOn (lg (n := n)) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hclosed : IsClosed {y : G n | lg y.val ≤ R} := by
    have : Continuous fun y : G n => lg y.val :=
      hlg.comp_continuous Units.continuous_val fun y => (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
    exact isClosed_le this continuous_const
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hK ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero) hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Loc
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Gam

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem iteratedDeriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (k : ℕ)
    (t : ℝ) : iteratedDeriv k (fun s => A (φ s)) t = A (iteratedDeriv k φ t) := by
  have h := (A.restrictScalars ℝ).iteratedFDeriv_comp_left (f := φ) (x := t) (i := k)
  have h2 := congrArg (fun L => L (fun _ : Fin k => (1 : ℝ))) h
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem deriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (t : ℝ) :
    deriv (fun s => A (φ s)) t = A (deriv φ t) := by
  have := iteratedDeriv_equiv A φ 1 t
  simpa only [iteratedDeriv_one] using this

theorem wave_equiv (E : KMod n) (A : E.V ≃L[ℂ] E.V) (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v))
    (u : ℝ → Mat n → E.V) (hu : IsWave E u) : IsWave E fun t x => A (u t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn h1
  · intro t
    refine ⟨(A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn (h2 t).1, ?_⟩
    intro g hg k
    simp only
    rw [(h2 t).2 g hg k, hA]
  · intro t g hg
    rw [iteratedDeriv_equiv A (fun s => u s g) 2 t, h3 t g hg, om_equiv]
  · intro g hg
    rw [deriv_equiv A (fun s => u s g) 0, h4 g hg, map_zero]

theorem act_equiv (hWE : WaveEx) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : E.V ≃L[ℂ] E.V)
    (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v)) (w : List (Bool × ℕ)) (g : ℝ → ℝ)
    (ks : Mat n → (E.V →L[ℂ] E.V)) (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (fun x => A (f x)) 1 = A (act μ E ks f 1) := by
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have hAu := wave_equiv E A hA u hu
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have key : ∀ F F' : Mat n → E.V, Set.EqOn F F' (GLs n) → act μ E ks F 1 = act μ E ks F' 1 := by
    intro F F' h
    unfold act
    congr 1
    funext y
    rw [h]
    simp only [GLs, Set.mem_setOf_eq, one_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  rw [key (fun x => A (f x)) (fun x => A (u 0 x)) (fun x hx => by simp only [hu0 x hx]),
    key f (u 0) (fun x hx => (hu0 x hx).symm),
    hks.2.2.2 _ hAu 1 hone, hks.2.2.2 _ hu 1 hone]
  refine Eq.trans ?_ (congrFun (zop_equiv A w _) 1)
  congr 2
  funext x'
  rw [← A.integral_comp_comm]
  congr 1
  funext t
  exact ((A : E.V →L[ℂ] E.V).map_smul_of_tower (g t) (u t x')).symm

end PositivityTheory.RgBcC.LfSt.ChainPf.Gam
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) :
    Set.EqOn (DC ε Fr f) (DC ε Fr f') U := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  simp only [DC, Rd, hev.fderiv_eq, h hx]

theorem cont_partial {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (x : Mat n) (hx : x ∈ GLs n) (X : Mat n) :
    Continuous (fun t => u t x) ∧ Continuous (fun t => Rd X (u t) x) := by
  have hs : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod (isOpen_GLs n)
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ GLs n) :=
    hu.continuousOn_fderiv_of_isOpen hs (by simp)
  have key : ∀ t, fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n)) := by
    intro t
    have hd : DifferentiableAt ℝ (Function.uncurry u) (t, x) :=
      (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ⟨Set.mem_univ _, hx⟩)
    exact (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hline : Continuous fun t : ℝ => ((t, x) : ℝ × Mat n) := continuous_id.prodMk continuous_const
  constructor
  · exact hu.continuousOn.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)
  · simp only [Rd, key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (hc.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)).clm_apply continuous_const

theorem bump_cpt (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T) : HasCompactSupport fun t => (g t : ℂ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
  intro t ht
  simp only [Complex.ofReal_eq_zero]
  exact hgb.2.2 t (by simpa [Real.norm_eq_abs, not_le] using ht)

theorem int_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (φ : ℝ → V) (hφ : Continuous φ) : Integrable fun t => (g t : ℂ) • φ t := by
  refine ((Complex.continuous_ofReal.comp hgb.1.continuous).smul hφ).integrable_of_hasCompactSupport ?_
  exact (bump_cpt g T hgb).smul_right

theorem param_dc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (hRd : ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x)
    (x : Mat n) (hx : x ∈ GLs n) :
    ∫ t, (g t : ℂ) • DC ε Fr (u t) x = DC ε Fr (fun x' => ∫ t, (g t : ℂ) • u t x') x := by
  have hc := fun X => cont_partial u hu x hx X
  have ia : ∀ X, Integrable (fun t => (g t : ℂ) • Rd X (u t) x) := fun X => int_bump g T hgb _ (hc X).2
  have ib : Integrable (fun t => (g t : ℂ) • u t x) := int_bump g T hgb _ (hc 0).1
  have iab : ∀ p : Fin n × Fin n, Integrable (fun t => (g t : ℂ) • Rd (hb p) (u t) x +
      (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) :=
    fun p => (ia _).add ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib)
  have hpt : ∀ t, (g t : ℂ) • DC ε Fr (u t) x = ∑ p : Fin n × Fin n, ε (hb p)
      ((g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) := by
    intro t
    simp only [DC, Finset.smul_sum, map_add (f := _), map_smul, smul_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun p _ => (ε (hb p)).integrable_comp (iab p))]
  simp only [DC, hRd _ x hx]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [(ε (hb p)).integral_comp_comm (iab p),
    integral_add (ia _) ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib),
    (fderiv ℝ Fr 1 (hb p)).integral_comp_comm ib]

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_of (y : G n) : y.val ∈ GLs n := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero

theorem mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem act_congr [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    {F F' : Mat n → E.V} (h : Set.EqOn F F' (GLs n)) {x : Mat n} (hx : x ∈ GLs n) : act μ E k F x = act μ E k F' x := by
  simp only [act]
  exact integral_congr_ae (Eventually.of_forall fun y => by
    show (k y.val) (F (x * y.val)) = (k y.val) (F' (x * y.val))
    rw [h (mul_mem_GLs hx (mem_GLs_of y))])

theorem act_dc (hDW : DCwave) (hP : ParamInt) (hZ : ZopDC) (hG : GelComm) (hWE : WaveEx) {lam : Fin n → ℤ} {E : KMod n}
    {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T' : ℝ) (hgb : IsBump g T') (ks : Mat n → (E.V →L[ℂ] E.V))
    (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (DC ε Fr f) 1 = DC ε Fr (act μ E ks f) 1 := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hDu := hDW hG n lam E Fr ε ι S Γ T hC u hu
  have hk1 := hks.2.2.2 _ hDu 1 h1
  obtain ⟨hPs, hPd⟩ := hP n E u hu g T' hgb
  have eqA : Set.EqOn (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') (GLs n) :=
    fun x hx => param_dc ε Fr u hu.1 g T' hgb hPd x hx
  have hz := hZ hG n lam E Fr ε ι S Γ T hC (fun x' => ∫ t, (g t : ℂ) • u t x') hPs w
  have eqB : Set.EqOn (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') (act μ E ks f) (GLs n) := by
    intro x hx
    rw [← hks.2.2.2 u hu x hx]
    exact act_congr μ E ks (fun y hy => hu0 y hy) hx
  have eq0 : Set.EqOn (DC ε Fr f) (DC ε Fr (u 0)) (GLs n) :=
    dc_congr ε Fr (isOpen_GLs n) fun y hy => (hu0 y hy).symm
  calc act μ E ks (DC ε Fr f) 1 = act μ E ks (DC ε Fr (u 0)) 1 := act_congr μ E ks eq0 h1
    _ = zOp w (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') 1 := hk1
    _ = zOp w (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') 1 := zop_congr (isOpen_GLs n) w eqA h1
    _ = DC ε Fr (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') 1 := hz.2 1 h1
    _ = DC ε Fr (act μ E ks f) 1 := dc_congr ε Fr (isOpen_GLs n) eqB h1

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Ker

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem int_of_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt f) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem act_one [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (F : Mat n → E.V) : act μ E k F 1 = ∫ y : G n, k y.val (F y.val) ∂μ := by
  simp only [act, one_mul]

theorem gamma_of_comm (hKZ : KerZero) (hL : LgFacts) {E : KMod n} (Γ : E.V →L[ℂ] E.V)
    (hΓρ : ∀ k, Γ * E.ρ k = E.ρ k * Γ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n))
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hΓ : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1)) :
    ∀ y ∈ GLs n, Γ * k y = k y * Γ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hz := hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub
      (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by
        simp only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by
      have hfcont : ContinuousOn f (GLs n) := hf.1.continuousOn
      have i1 := int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc
      have i2 := int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub i1 i2]
      have e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1 := by
        rw [act_one]; rfl
      have e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1) := by
        rw [act_one]
        exact ContinuousLinearMap.integral_comp_comm Γ
          (int_of_cpt hL μ k f hkc hfcont hfc)
      rw [e1, e2, hΓ f hf, sub_self])
  intro y hy
  have := hz y hy
  exact (sub_eq_zero.1 this).symm

theorem rd_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Rd X f) (GLs n) :=
  (hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_id.matrix_mul continuous_const).continuousOn

theorem ld_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Ld X f) (GLs n) :=
  ((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_const.matrix_mul continuous_id).continuousOn).neg

def mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
  (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip A

theorem rd_mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V))
    (hk : ContDiffOn ℝ ∞ k (GLs n)) (A : V →L[ℂ] V) (X : Mat n) (y : Mat n) (hy : y ∈ GLs n) :
    Rd X (fun y => k y * A) y = Rd X k y * A := by
  have hd : DifferentiableAt ℝ k y := (hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)
  have e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k := rfl
  have hd2 := (((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [Rd]
  rw [e]
  exact congrArg (fun L => L (y * X)) hd2

theorem kapL_int (hA : ActDer) (hU : Unimod) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    DC ε Fr (act μ E k f) 1 = ∫ y : G n, kapL ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hD := (hA hU n μ E k f hks hkc hf).2
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc
  have iK : Integrable (fun y : G n => k y.val (f y.val)) μ := int_of_cpt hL μ _ f hks.continuousOn hfc' hfc
  have iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ := fun p =>
    ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val))) := by
    intro y
    simp [kapL]
  simp_rw [ek]
  rw [integral_finsetSum _ fun p _ => iP p]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ :=
    integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)
  have e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ =
      ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ iK
  rw [e1, e2, e3, hD _ 1 h1, act_one]
  simp only [one_mul]

theorem int_of_cptK (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt K) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem kapR_int (hI : IBPAct) (hU : Unimod) (hR : RCalc) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    act μ E k (DC ε Fr f) 1 = ∫ y : G n, kapR ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n) := fun p => by
    have e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k := rfl
    rw [e]
    exact ((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks
  have hkc' : ∀ p, Cpt fun y => k y * ε (hb p) := fun p => by
    obtain ⟨R, hR⟩ := hkc
    exact ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ := fun p =>
    int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)
  have iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc
  have iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc
  have eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [DC, map_sum, map_add (f := _)]
  have eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [kapR]
  rw [act_one]
  simp_rw [eL, eR]
  have sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iA p).add (iB p)
  have sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iC p).neg.add (iB p)
  rw [sL, sR]
  refine Finset.sum_congr rfl fun p _ => ?_
  have a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iA p) (iB p)
  have a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iC p).neg (iB p)
  rw [a1, a2, integral_neg]
  congr 1
  have hibp := hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1
  simp only [one_mul] at hibp
  rw [hibp]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)
  rw [rd_mr k hks _ _ _ (mem_GLs_of y)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Ker
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Top

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_of_comm (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hKZ : KerZero) (hU : Unimod) (hR : RCalc)
    (hL : LgFacts) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)]
    [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
    (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hD : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1) :
    ∀ y ∈ GLs n, kapL ε Fr k y = kapR ε Fr k y := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨cL, cR, heq⟩ := hK n lam E Fr ε ι S Γ T hC k hks hke
  have hz := hKZ n μ E (fun y => kapL ε Fr k y - kapR ε Fr k y) (cL.sub cR)
    (fun y hy k₂ => by simp only [(heq y hy k₂).1, (heq y hy k₂).2, sub_mul]) (fun f hf hfc => by
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub (int_of_cpt hL μ _ f cL hf.1.continuousOn hfc) (int_of_cpt hL μ _ f cR hf.1.continuousOn hfc),
        ← kapL_int hA hU hL Fr ε μ k hks hkc f hf.1 hfc, ← kapR_int hI hU hR hL Fr ε μ k hks hkc f hf.1 hfc, hD f hf,
        sub_self])
  exact fun y hy => sub_eq_zero.1 (hz y hy)

end PositivityTheory.RgBcC.LfSt.ChainPf.Top
