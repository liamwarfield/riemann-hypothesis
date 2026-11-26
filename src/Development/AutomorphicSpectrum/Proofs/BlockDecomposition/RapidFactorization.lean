module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorization
noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

def phaseRoot (z : ℂ) : ℂ := z / ((Real.sqrt ‖z‖ : ℝ) : ℂ)

theorem norm_phaseRoot (z : ℂ) : ‖phaseRoot z‖ = Real.sqrt ‖z‖ := by
  unfold phaseRoot
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.div_sqrt

theorem continuous_phaseRoot : Continuous phaseRoot := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : phaseRoot 0 = 0 := by simp [phaseRoot]
    unfold ContinuousAt
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_phaseRoot]
    have : Continuous fun w : ℂ => Real.sqrt ‖w‖ := by fun_prop
    simpa using this.tendsto 0
  · have hne : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
      exact_mod_cast this.ne'
    have hc : Continuous fun w : ℂ => ((Real.sqrt ‖w‖ : ℝ) : ℂ) := by fun_prop
    exact continuousAt_id.div hc.continuousAt hne

theorem tendsto_pow_mul_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ}
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * k y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨h', hh'⟩ := hr (2 * m)
  have h0 : Tendsto (fun y => ‖h' y‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (h'.zero_at_infty')
  have h1 : Tendsto (fun y => Real.sqrt ‖h' y‖) (cocompact ℝ) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h1.congr fun y => ?_
  rw [hh', norm_mul, norm_mul, hn, norm_pow, norm_pow, Complex.norm_real, pow_mul',
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem exists_rapid_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ} (hc : Continuous k)
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) : ∃ k' : C₀(ℝ, ℂ), (∀ y, k' y = k y) ∧ Rapid k' := by
  have key : ∀ m : ℕ, ∃ g : C₀(ℝ, ℂ), ∀ y, g y = (y : ℂ) ^ m * k y := fun m =>
    ⟨⟨⟨fun y => (y : ℂ) ^ m * k y, by fun_prop⟩, tendsto_pow_mul_of_norm_sqrt hr hn m⟩,
      fun _ => rfl⟩
  obtain ⟨k', hk'⟩ := key 0
  have hk : ∀ y, k' y = k y := fun y => by simp [hk']
  refine ⟨k', hk, fun m => ?_⟩
  obtain ⟨g, hg⟩ := key m
  exact ⟨g, fun y => by rw [hg, hk]⟩

theorem factorRapid : FactorRapid := by
  intro h hr
  obtain ⟨h₁, e₁, r₁⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => phaseRoot (h y))
    (continuous_phaseRoot.comp h.continuous) (fun y => norm_phaseRoot _)
  obtain ⟨h₂, e₂, r₂⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => ((Real.sqrt ‖h y‖ : ℝ) : ℂ))
    (by have := h.continuous; fun_prop)
    (fun y => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)])
  have hs : star h₂ = h₂ := by
    ext y
    rw [ZeroAtInftyContinuousMap.star_apply, e₂]
    simp
  refine ⟨h₁, h₂, r₁, r₂, by rwa [hs], ?_⟩
  ext y
  rw [ZeroAtInftyContinuousMap.mul_apply, e₁, e₂]
  by_cases hy : h y = 0
  · simp [hy, phaseRoot]
  · have hne : ((Real.sqrt ‖h y‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖h y‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)
      exact_mod_cast this.ne'
    simp only [phaseRoot]
    field_simp

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorizationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapid_factorization : GlobalTheory.CompanionTheory.KerFc.FactorRapid := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.factorRapid | exact GlobalTheory.CompanionTheory.KerFc.factorRapid | (intros; apply GlobalTheory.CompanionTheory.KerFc.factorRapid <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTranslateSobolev

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem val_mem (x : G n) : x.val ∈ GLs n := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact h.ne_zero

def mulL (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := fun y z => Matrix.mul_add a y z
      map_smul' := fun c y => Matrix.mul_smul a c y }

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (lTr x f) (GLs n) :=
  hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)

theorem Rd_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n)
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (lTr x f) g = Rd X f (x.val * g) := by
  have hxg : x.val * g ∈ GLs n := mul_mem (val_mem x) hg
  have hd : DifferentiableAt ℝ f (mulL x.val g) :=
    (hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)
  have hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val) :=
    (hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv
  show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)
  rw [hc]
  simp [mulL, Matrix.mul_assoc]

theorem contDiffOn_Rw (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)

theorem Rw_lTr (hR : RCalc) (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ∀ g ∈ GLs n, Rw w (lTr x f) g = Rw w f (x.val * g) := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f) :=
      Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)
    show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)
    rw [← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]
    show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)
    rw [he.fderiv_eq]

end LeftTranslateSobolev


open LeftTranslateSobolev in
theorem ltSob : LtSob := by
  intro n _ _ μ _ V _ _ _ _ hR x f hf
  refine ⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩
  · have h := (hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)
    have he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y) :=
      funext fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)
    rw [he]
    exact h
  · have ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g) := fun s =>
      (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1
    simp only [Om, Pi.smul_apply, Pi.add_apply, ht]

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolevStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_sobolev : GlobalTheory.CompanionTheory.KerFc.LtSob := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltSob <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem riesz_of_relation {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (S : Submodule ℂ H) (R : H → V → Prop) (C : ℝ)
    (hex : ∀ x ∈ closure (S : Set H), ∃ w, R x w ∧ ‖w‖ ≤ C * ‖x‖)
    (huniq : ∀ x w w', R x w → R x w' → w = w')
    (hlin : ∀ (a : ℂ) x y w w', R x w → R y w' → R (a • x + y) (a • w + w')) (v : V) :
    ∃ κ ∈ closure (S : Set H), ∀ x ∈ S, ∀ w, R x w → ⟪κ, x⟫_ℂ = ⟪v, w⟫_ℂ := by
  classical
  have hK : ∀ x : S.topologicalClosure, ∃ w, R (x : H) w ∧ ‖w‖ ≤ C * ‖(x : H)‖ := fun x =>
    hex x x.2
  choose l hl hb using hK
  have hl0 : l 0 = 0 := by
    have := hb 0
    simpa using this
  let L₀ : S.topologicalClosure →ₗ[ℂ] V :=
    { toFun := l
      map_add' := fun x y => by
        have := hlin 1 x y (l x) (l y) (hl x) (hl y)
        exact huniq _ _ _ (hl (x + y)) (by simpa using this)
      map_smul' := fun a x => by
        have := hlin a x 0 (l x) (l 0) (hl x) (hl 0)
        exact huniq _ _ _ (hl (a • x)) (by simpa [hl0] using this) }
  let L : S.topologicalClosure →L[ℂ] V := L₀.mkContinuous C (fun x => hb x)
  refine ⟨(ContinuousLinearMap.adjoint L v : S.topologicalClosure), ?_, ?_⟩
  · exact (ContinuousLinearMap.adjoint L v).2
  · intro x hx w hw
    have hxk : x ∈ S.topologicalClosure := S.le_topologicalClosure hx
    have hw' : w = l ⟨x, hxk⟩ := huniq x w _ hw (hl ⟨x, hxk⟩)
    have := ContinuousLinearMap.adjoint_inner_left L (⟨x, hxk⟩ : S.topologicalClosure) v
    rw [hw']
    exact this

theorem Rw_zero {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp [Rw, ih, Rd]

theorem sob_zero {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Sob μ (0 : Mat n → V) := by
  refine ⟨contDiffOn_const, fun w => ?_⟩
  rw [Rw_zero]
  exact MemLp.zero

theorem evAdj : EvAdj := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  obtain ⟨hLg, hUn, hRC, hSob, hAlg, hWS, hWC, hCS, hSm, hPW, hM, hsym, hres, hinv, hOm, hbd⟩ := hS
  obtain ⟨C, hC⟩ := hSm n μ E Ω T F hLg hUn hRC hSob hAlg hCS hOm h hh
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  obtain ⟨hc1, hc2, -⟩ := hCl n μ E.V hUn
  have hmem : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  have hsum : ∀ (a : ℂ) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → Sob μ (a • f + f') := fun a f f' hf hf' =>
    ((hOps n μ E.V hLg hUn hRC f hf).2.2.2.1 a f' hf').1
  have hsec : ∀ (a : ℂ) (f f' : Mat n → E.V), IsSec E f → IsSec E f' → IsSec E (a • f + f') := by
    intro a f f' hf hf' g hg k
    simp [hf g hg k, hf' g hg k]
  have h0 : cls μ (0 : Mat n → E.V) = 0 := by
    simpa using hc2 (-1) 0 0 (hmem (sob_zero μ E.V)) (hmem (sob_zero μ E.V))
  let S : Submodule ℂ (Lp E.V 2 μ) :=
    { carrier := secCls μ E
      zero_mem' := ⟨0, sob_zero μ E.V, fun g _ k => by simp, h0⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, hs, rfl⟩ ⟨f', hf', hs', rfl⟩
        exact ⟨1 • f + f', hsum 1 f f' hf hf', hsec 1 f f' hs hs', by
          simpa using hc2 1 f f' (hmem hf) (hmem hf')⟩
      smul_mem' := by
        rintro a _ ⟨f, hf, hs, rfl⟩
        refine ⟨a • f + 0, hsum a f 0 hf (sob_zero μ E.V), hsec a f 0 hs (fun g _ k => by simp), ?_⟩
        have := hc2 a f 0 (hmem hf) (hmem (sob_zero μ E.V))
        simpa [h0] using this }
  let R : Lp E.V 2 μ → E.V → Prop := fun x w =>
    ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h x ∧ f' 1 = w
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  obtain ⟨κ, hκ, hrep⟩ := riesz_of_relation S R C
    (fun x hx => by
      obtain ⟨f', a, b, d, e⟩ := hC x hx
      exact ⟨f' 1, ⟨f', a, b, d, rfl⟩, e⟩)
    (by
      rintro x _ _ ⟨f, hf, -, hcf, rfl⟩ ⟨f', hf', -, hcf', rfl⟩
      exact hc1 f f' hf.1.continuousOn hf'.1.continuousOn (hmem hf) (hmem hf') (hcf.trans hcf'.symm) 1 h1)
    (by
      rintro a x y _ _ ⟨f, hf, hs, hcf, rfl⟩ ⟨f', hf', hs', hcf', rfl⟩
      refine ⟨a • f + f', hsum a f f' hf hf', hsec a f f' hs hs', ?_, rfl⟩
      rw [hc2 a f f' (hmem hf) (hmem hf'), hcf, hcf', map_add (f := _), map_smul]) v
  refine ⟨κ, hκ, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  exact hrep (cls μ φ) ⟨φ, hφ, hφs, rfl⟩ (f' 1) ⟨f', hf', hf's, hcl, rfl⟩

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_adjoint_facts : GlobalTheory.CompanionTheory.KerFc.EvAdj := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.evAdj | exact GlobalTheory.CompanionTheory.KerFc.evAdj | (intros; apply GlobalTheory.CompanionTheory.KerFc.evAdj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def unitaryUnit {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : G n :=
  ⟨k.1, (k⁻¹).1,
    by have h : (k * k⁻¹).1 = 1 := by rw [mul_inv_cancel]; rfl
       exact h,
    by have h : (k⁻¹ * k).1 = 1 := by rw [inv_mul_cancel]; rfl
       exact h⟩

theorem unitaryUnit_inv_val {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((unitaryUnit k)⁻¹ : G n).val = (k⁻¹).1 := rfl

theorem inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (f g : Mat n → V) (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left hg, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) (f g : Mat n → V)
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => lTr x f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) (hg' : MemLp (fun y : G n => lTr x⁻¹ g y.val) 2 μ) :
    ⟪cls μ (lTr x f), cls μ g⟫_ℂ = ⟪cls μ f, cls μ (lTr x⁻¹ g)⟫_ℂ := by
  rw [inner_cls μ _ _ hf' hg, inner_cls μ _ _ hf hg',
    ← integral_mul_left_eq_self (μ := μ) (fun y : G n => ⟪f y.val, lTr x⁻¹ g y.val⟫_ℂ) x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h : (x⁻¹ : G n).val * (x.val * y.val) = y.val := by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_left]
  simp only [lTr, Units.val_mul, h]

theorem isSec_lTr {n : ℕ} {E : KMod n} (x : G n) {f : Mat n → E.V} (hf : IsSec E f) : IsSec E (lTr x f) := by
  intro g hg k
  have hxg : x.val * g ∈ GLs n := by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hg ⊢
    exact mul_ne_zero (Matrix.isUnits_det_units x).ne_zero hg
  have := hf _ hxg k
  simpa only [lTr, mul_assoc] using this

theorem inner_rho {n : ℕ} (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (v w : E.V) :
    ⟪v, E.ρ k w⟫_ℂ = ⟪E.ρ k⁻¹ v, w⟫_ℂ := by
  have hI : ∀ a b : E.V, ⟪E.ρ k a, E.ρ k b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    LinearIsometry.inner_map_map (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V) a b
  have h1 : E.ρ k (E.ρ k⁻¹ v) = v := by
    have h := map_mul E.ρ k k⁻¹
    rw [mul_inv_cancel, map_one] at h
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => S v) h
    simpa using h2.symm
  rw [← hI (E.ρ k⁻¹ v) w, h1]

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem rowLeft (hLS : LtSob) (hLC : LtComm) : RowLeft := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hR hRow k y hy v
  have hStd' := hStd
  obtain ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hS1, hS2, hS3, hS4, hOm, hc⟩ := hStd'
  have hCF := hCS.2.2.2.2.1 n μ E.V hUn
  have hSB := hCS.2.2.2.2.2.1 n μ E.V hLg hUn hRC
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h hR
  have hLt := hLS n μ E.V hLg hUn hRC
  have hL2 : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  set x : G n := unitaryUnit k with hx
  set r : Mat n → E.V := fun y => A y v with hr
  set b : Mat n → E.V := fun y => A y (E.ρ k⁻¹ v) with hb
  set a : Mat n → E.V := lTr x r with ha
  have hrow := hRow v
  have hrowb := hRow (E.ρ k⁻¹ v)
  have hrS : Sob μ r := hrow.1
  have hbS : Sob μ b := hrowb.1
  have haS : Sob μ a := (hLt x r hrS).1
  have haSec : IsSec E a := isSec_lTr x hrow.2.1
  have hkey : ∀ ψ : Mat n → E.V, Sob μ ψ → IsSec E ψ → ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ b, cls μ ψ⟫_ℂ := by
    intro ψ hψ hψs
    obtain ⟨ψ', hψ'S, hψ's, hψ'c, -⟩ := hC (cls μ ψ) (subset_closure ⟨ψ, hψ, hψs, rfl⟩)
    have hlψ := (hLt x⁻¹ ψ hψ).1
    have hlψ' := (hLt x⁻¹ ψ' hψ'S).1
    have hcomm := hLC n μ E Ω T F c hStd h x⁻¹ ψ ψ' hψ hψ'S hψ'c
    have e1 : ⟪cls μ a, cls μ ψ⟫_ℂ = ⟪cls μ r, cls μ (lTr x⁻¹ ψ)⟫_ℂ :=
      inner_cls_lTr μ x r ψ (hL2 hrS) (hL2 haS) (hL2 hψ) (hL2 hlψ)
    have e2 := hrow.2.2 (lTr x⁻¹ ψ) (lTr x⁻¹ ψ') hlψ (isSec_lTr _ hψs) hlψ' (isSec_lTr _ hψ's) hcomm
    have e3 : lTr x⁻¹ ψ' 1 = E.ρ k (ψ' 1) := by
      have h1 := hψ's 1 (one_mem_GLs n) k⁻¹
      rw [inv_inv, one_mul] at h1
      simpa only [lTr, mul_one, hx, unitaryUnit_inv_val] using h1
    have e4 := hrowb.2.2 ψ ψ' hψ hψs hψ'S hψ's hψ'c
    rw [e1, e2, e3, inner_rho, ← e4]
  set ψ : Mat n → E.V := (-1 : ℂ) • b + a with hψd
  have hψS : Sob μ ψ := ((hSB b hbS).2.2.2.1 (-1) a haS).1
  have hbSec : IsSec E b := hrowb.2.1
  have hψs : IsSec E ψ := by
    intro g hg k'
    simp only [hψd, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul]
    rw [hbSec g hg k', haSec g hg k']
  have hcψ : cls μ ψ = cls μ a - cls μ b := by
    rw [hψd, hCF.2.1 (-1) b a (hL2 hbS) (hL2 haS)]
    simp [sub_eq_add_neg, add_comm]
  have hz := hkey ψ hψS hψs
  have hzero : cls μ a - cls μ b = 0 := by
    rw [hcψ] at hz
    have : ⟪cls μ a - cls μ b, cls μ a - cls μ b⟫_ℂ = 0 := by
      rw [inner_sub_left, hz, sub_self]
    exact inner_self_eq_zero.mp this
  have hfin := hCF.1 a b haS.1.continuousOn hbS.1.continuousOn (hL2 haS) (hL2 hbS) (sub_eq_zero.mp hzero) y hy
  exact hfin

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_left_invariant : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.RowLeft := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowLeft | exact GlobalTheory.CompanionTheory.KerFc.rowLeft | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowLeft <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ZeroAtInfty InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveLoc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  have hx' : x.det ≠ 0 := hx
  have hy' : y.det ≠ 0 := hy
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx' hy'

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.mpr hx)).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

def step (r s : ℝ) : ℝ := Real.smoothTransition (r + 1 - s)

theorem step_contDiff (r : ℝ) : ContDiff ℝ ∞ (step r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem step_eq_one {r s : ℝ} (h : s ≤ r) : step r s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {r s : ℝ} (h : r + 1 ≤ s) : step r s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def cutAt (r : ℝ) (x y : Mat n) : ℝ := step r (lg (x⁻¹ * y))

theorem cutAt_smooth (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (cutAt r x) (GLs n) := by
  have hm : ContDiff ℝ ∞ (fun y : Mat n => x⁻¹ * y) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x⁻¹)).contDiff
  have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    (hL n).2.2.2.1.comp hm.contDiffOn fun _ hy => mul_mem (inv_mem hx) hy
  exact (step_contDiff r).comp_contDiffOn h1

theorem cutAt_mul_unitary (hL : LgFacts) (r : ℝ) {x g : Mat n} (hx : x ∈ GLs n) (hg : g ∈ GLs n)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : cutAt r x (g * k.1) = cutAt r x g := by
  have h := (hL n).2.2.1 (x⁻¹ * g) (mul_mem (inv_mem hx) hg) 1 k
  have e : ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 * (x⁻¹ * g) * k.1 = x⁻¹ * (g * k.1) := by
    rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 = 1 from rfl, one_mul, mul_assoc]
  rw [e] at h
  simp only [cutAt, h]

def cutSec {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (r : ℝ) (x : Mat n) (f : Mat n → V) : Mat n → V :=
  fun y => ((cutAt r x y : ℝ) : ℂ) • f y

theorem cutSec_mem (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {E : KMod n} {f : Mat n → E.V}
    (hf : f ∈ CE E) : cutSec r x f ∈ CE E := by
  refine ⟨?_, fun g hg k => ?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun y => ((cutAt r x y : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (cutAt_smooth hL r hx)
    exact hc.smul hf.1
  · simp only [cutSec, cutAt_mul_unitary hL r hx hg k, hf.2 g hg k, map_smul]

theorem cutSec_cpt (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (f : Mat n → V) : Cpt (cutSec r x f) := by
  refine ⟨lg x + (r + 1), fun y hy h => ?_⟩
  have e : x * (x⁻¹ * y) = y := Matrix.mul_nonsing_inv_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have hs := (hL n).1 x hx (x⁻¹ * y) (mul_mem (inv_mem hx) hy)
  rw [e] at hs
  have h0 : cutAt r x y = 0 := step_eq_zero (by linarith)
  simp [cutSec, h0]

theorem cutSec_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ} {x y : Mat n} (hx : x ∈ GLs n)
    (f : Mat n → V) (h : lg y ≤ r) : cutSec r x f (x * y) = f (x * y) := by
  have e : x⁻¹ * (x * y) = y := Matrix.nonsing_inv_mul_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have h1 : cutAt r x (x * y) = 1 := by
    rw [cutAt, e]
    exact step_eq_one h
  simp [cutSec, h1]

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y - v t y := by
  have h := GlobalTheory.CompanionTheory.WaveK.Lin.wave_add hu (GlobalTheory.CompanionTheory.WaveK.Lin.wave_smul (-1 : ℂ) hv)
  simpa [sub_eq_add_neg] using h

theorem kerLoc : KerLoc := by
  intro n _ _ μ _ E g T k hg hL _ _ hS hW hk hsupp heq hker
  refine ⟨hk, hsupp, heq, fun u hu x hx => ?_⟩
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨c, hc⟩ := hS n
  obtain ⟨r, hRr, hcr⟩ : ∃ r : ℝ, R ≤ r ∧ |c| * (1 + |T|) ≤ r :=
    ⟨max R (|c| * (1 + |T|)), le_max_left _ _, le_max_right _ _⟩
  have hf := cutSec_mem hL r hx (hu.2.1 0)
  have hcpt := cutSec_cpt hL r hx (u 0)
  obtain ⟨v, hv, hv0⟩ := hW n E _ hf hcpt
  have huv : ∀ t, |t| ≤ T → u t x = v t x := by
    intro t ht
    refine sub_eq_zero.mp (hc E _ (wave_sub hu hv) t x hx fun y hy hly => ?_)
    have hb : c * (1 + |t|) ≤ |c| * (1 + |T|) := by
      have h1 : |t| ≤ |T| := ht.trans (le_abs_self T)
      have h2 : (0 : ℝ) ≤ 1 + |t| := by positivity
      calc c * (1 + |t|) ≤ |c| * (1 + |t|) := mul_le_mul_of_nonneg_right (le_abs_self c) h2
        _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    show u 0 (x * y) - v 0 (x * y) = 0
    rw [hv0 _ (mul_mem hx hy), cutSec_eq hx _ (hly.trans (hb.trans hcr)), sub_self]
  have h1 : act μ E k (u 0) x = act μ E k (cutSec r x (u 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show k y.val (u 0 (x * y.val)) = k y.val (cutSec r x (u 0) (x * y.val))
    by_cases h : R < lg y.val
    · simp [hR _ (val_mem y) h]
    · rw [cutSec_eq hx _ ((not_lt.mp h).trans hRr)]
  rw [h1, hker _ hf hcpt v hv hv0 x hx]
  show _ = ∫ t, (g t : ℂ) • u t x
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (g t : ℂ) • v t x = (g t : ℂ) • u t x
  by_cases h : T < |t|
  · simp [hg.2.2 t h]
  · rw [huv t (not_lt.mp h)]

end GlobalTheory.CompanionTheory.WaveLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalizationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_localization : PositivityTheory.RgBcC.Fc.KerLoc := by
  first | exact @GlobalTheory.CompanionTheory.WaveLoc.kerLoc | exact GlobalTheory.CompanionTheory.WaveLoc.kerLoc | (intros; apply GlobalTheory.CompanionTheory.WaveLoc.kerLoc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupport
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma sr_window {R a : ℝ} (h : R < a) : ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ s, 0 ≤ β s) ∧ 0 < β a ∧
    (∀ s, s ≤ R → β s = 0) ∧ ∀ s, a + 1 ≤ s → β s = 0 := by
  refine ⟨fun s => Real.smoothTransition (s - R) * Real.smoothTransition (a + 1 - s), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  · intro s
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
      (Real.smoothTransition.pos_of_pos (by linarith))
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith), zero_mul]
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show a + 1 - s ≤ 0 by linarith), mul_zero]

lemma sr_inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f g : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    Integrable (fun y : G n => ⟪f y.val, g y.val⟫_ℂ) μ ∧
      ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := dif_pos hf
  have e2 : cls μ g = hg.toLp _ := dif_pos hg
  have hae : (fun y : G n => ⟪(hf.toLp _ : Lp V 2 μ) y, (hg.toLp _ : Lp V 2 μ) y⟫_ℂ) =ᵐ[μ]
      fun y : G n => ⟪f y.val, g y.val⟫_ℂ := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b
    rw [a, b]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)).congr hae, ?_⟩
  rw [e1, e2, L2.inner_def]
  exact integral_congr_ae hae

lemma sr_val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

lemma sr_eq_zero {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {ψ : G n → ℝ} (hc : Continuous ψ) (h0 : ∀ y, 0 ≤ ψ y) (hi : Integrable ψ μ) (hz : ∫ y, ψ y ∂μ = 0) :
    ∀ y, ψ y = 0 := by
  have hae : ψ =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg h0 hi).1 hz
  have := (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 hae
  intro y
  rw [this]
  rfl

theorem supportRow : SupportRow := by
  intro n _ _ μ _ E _ Ω T F c hStd g T₀ h hg hh H
  obtain ⟨hLg, hUn, hRC, hSobG, hAlg, hWS, hWC, hCS, hSO, hPW, -, -, -, -, hOm, -⟩ := hStd
  have hCptSob : CptSob := hCS.2.2.2.2.2.2.1
  obtain ⟨c₀, hc₀⟩ := hWS n
  refine ⟨|c₀| * (1 + |T₀|), ?_⟩
  intro v f hRow y₀ hy₀ hR
  obtain ⟨hfSob, hfSec, hfRow⟩ := hRow
  obtain ⟨β, hβs, hβ0, hβpos, hβlo, hβhi⟩ := sr_window hR
  obtain ⟨-, -, hLk, hLs, -, -, -⟩ := hLg n
  set φ : Mat n → E.V := fun y => ((β (lg y) : ℝ) : ℂ) • f y with hφ

  have hφs : ContDiffOn ℝ ∞ φ (GLs n) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => ((β (lg y) : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hβs.comp_contDiffOn hLs)
    exact h1.smul hfSob.1
  have hφsec : IsSec E φ := by
    intro y hy k
    have hl : lg (y * k.1) = lg y := by
      have := hLk y hy 1 k
      simpa using this
    simp only [hφ, hl, hfSec y hy k, map_smul]
  have hφc : Cpt φ := by
    refine ⟨lg y₀ + 1, fun y _ hy => ?_⟩
    simp only [hφ, hβhi _ hy.le, Complex.ofReal_zero, zero_smul]
  have hφCE : φ ∈ CE E := ⟨hφs, hφsec⟩
  have hφSob : Sob μ φ := (hCptSob n μ E.V hLg hRC φ hφs hφc).1
  obtain ⟨u, huW, hu0⟩ := hWC n E φ hφCE hφc
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSobG hAlg hCS hOm h hh
  obtain ⟨f', hf'Sob, hf'Sec, hf'cls, -⟩ := hC (cls μ φ) (subset_closure ⟨φ, hφSob, hφsec, rfl⟩)
  have h1G : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp

  have hf'1 : f' 1 = 0 := by
    rw [← H φ hφCE hφc u huW hu0 f' hf'Sob hf'Sec hf'cls 1 h1G]
    have : ∀ t, (g t : ℂ) • u t 1 = 0 := by
      intro t
      by_cases hgt : g t = 0
      · simp [hgt]
      · have ht : |t| ≤ T₀ := by
          by_contra hcon
          exact hgt (hg.2.2 t (not_le.1 hcon))
        have hut : u t 1 = 0 := by
          refine hc₀ E u huW t 1 h1G fun y hy hly => ?_
          rw [one_mul, hu0 y hy]
          have hb : lg y ≤ |c₀| * (1 + |T₀|) := by
            refine hly.trans ?_
            have h1 : c₀ ≤ |c₀| := le_abs_self _
            have h2 : |t| ≤ |T₀| := ht.trans (le_abs_self _)
            have h3 : 0 ≤ |c₀| := abs_nonneg _
            have h4 : 0 ≤ |t| := abs_nonneg _
            nlinarith
          simp only [hφ, hβlo _ hb, Complex.ofReal_zero, zero_smul]
        simp [hut]
    simp [this]
  have hzero : ⟪cls μ f, cls μ φ⟫_ℂ = 0 := by
    rw [hfRow φ f' hφSob hφsec hf'Sob hf'Sec hf'cls, hf'1, inner_zero_right]

  have hfL : MemLp (fun y : G n => f y.val) 2 μ := hfSob.2 []
  have hφL : MemLp (fun y : G n => φ y.val) 2 μ := hφSob.2 []
  obtain ⟨hI, hE⟩ := sr_inner_cls μ hfL hφL
  set ψ : G n → ℝ := fun y => β (lg y.val) * ‖f y.val‖ ^ 2 with hψ
  have hpt : ∀ y : G n, ⟪f y.val, φ y.val⟫_ℂ = (ψ y : ℂ) := by
    intro y
    simp only [hφ, hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hψi : Integrable ψ μ := by
    have := hI.re
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [hpt y]
  have hψz : ∫ y, ψ y ∂μ = 0 := by
    have h2 : ((∫ y, ψ y ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hzero, hE]
      exact integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    exact_mod_cast h2
  have hlc : Continuous (fun y : G n => lg y.val) :=
    hLs.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hfc : Continuous (fun y : G n => f y.val) :=
    hfSob.1.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hψc : Continuous ψ := (hβs.continuous.comp hlc).mul (hfc.norm.pow 2)
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (hβ0 _) (by positivity)
  have hall := sr_eq_zero μ hψc hψ0 hψi hψz
  have := hall (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀)
  have hval : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀ : G n).val = y₀ := rfl
  simp only [hψ, hval] at this
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hβpos.ne'
  · simpa using h'

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupportStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_support : GlobalTheory.CompanionTheory.KerFc.SupportRow := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.supportRow | exact GlobalTheory.CompanionTheory.KerFc.supportRow | (intros; apply GlobalTheory.CompanionTheory.KerFc.supportRow <;> assumption)
end
end
