module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecay
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEq
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KAvgDeriv

open MeasureTheory Filter Topology GlobalTheory.KFourier

variable {n : ℕ}

theorem toMK_expK_real {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp (t • X) := by
  rw [toMK_expK hX t, Complex.coe_smul]

theorem toMK_mem_UJ {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integral_conj_swap {ε : Fin n → Bool} (e : KG ε → ℂ) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k)
    (φ : Mx n → ℂ) (g : Mx n) (κ : KG ε) :
    ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε) = ∫ k, e k * φ (g * toMK k * toMK κ) ∂(muK ε) := by
  have h1 := integral_mul_left_eq_self (μ := muK ε) (fun k => e k * φ (g * toMK κ * toMK k)) κ⁻¹
  have h2 := integral_mul_right_eq_self (μ := muK ε) (fun k => e (κ⁻¹ * k) * φ (g * toMK k)) κ
  have ea : ∀ k, g * toMK κ * toMK (κ⁻¹ * k) = g * toMK k := fun k => by
    rw [mul_assoc, ← toMK_mul, mul_inv_cancel_left]
  have eb : ∀ k, e (κ⁻¹ * (k * κ)) = e k := fun k => by
    have := he κ⁻¹ k
    rwa [inv_inv, mul_assoc] at this
  calc ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε)
      = ∫ k, e (κ⁻¹ * k) * φ (g * toMK κ * toMK (κ⁻¹ * k)) ∂(muK ε) := h1.symm
    _ = ∫ k, e (κ⁻¹ * k) * φ (g * toMK k) ∂(muK ε) := by simp only [ea]
    _ = ∫ k, e (κ⁻¹ * (k * κ)) * φ (g * toMK (k * κ)) ∂(muK ε) := h2.symm
    _ = _ := by simp only [eb, toMK_mul, mul_assoc]

variable {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ}

theorem measurable_fam (hD : IsDerFam ε F) {f : Mx n → ℂ} (hf : ContinuousOn f (UJset ε))
    (hF0 : ∀ g ∈ UJset ε, F [] g = f g) :
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      Measurable fun k : KG ε => F l (a * toMK k * b) := by
  intro l
  induction l with
  | nil =>
    intro _ a ha b hb
    have hm : ∀ k : KG ε, a * toMK k * b ∈ UJset ε := fun k => mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have e1 : (fun k : KG ε => F [] (a * toMK k * b)) = fun k => f (a * toMK k * b) :=
      funext fun k => hF0 _ (hm k)
    rw [e1]
    exact (hf.comp_continuous ((continuous_const.mul (continuous_toMK ε)).mul continuous_const) hm).measurable
  | cons X l ih =>
    intro hl a ha b hb
    have hX : X ∈ lieSet ε := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hs0 : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun m => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, s]; positivity⟩
    have hmeas : ∀ m : ℕ, Measurable fun k : KG ε =>
        (s m)⁻¹ • (F l (a * toMK k * (b * NormedSpace.exp (s m • X))) - F l (a * toMK k * b)) := fun m => by
      have := ((ih hl' a ha _ (mul_mem_UJ hb (exp_mem_UJ hX (s m)))).sub (ih hl' a ha b hb)).const_smul (s m)⁻¹
      exact this
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun k => ?_)
    have hg : a * toMK k * b ∈ UJset ε := mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hD l hl' X hX _ hg)).comp hs0
    refine hd.congr fun m => ?_
    simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
      mul_assoc]

theorem hasDerivAt_avg (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n}
    (hX : inK ε X) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε))
      (∫ k, e k * F (X :: l) (g * toMK k) ∂(muK ε)) 0 := by
  have hXl : X ∈ lieSet ε := hX.1
  have hl' : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hXl, hl Y h]
  have hre : (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε)) =
      fun t => ∫ k, e k * F l (g * toMK k * NormedSpace.exp (t • X)) ∂(muK ε) := by
    funext t
    rw [integral_conj_swap e he, toMK_expK_real hX]
  rw [hre]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨C, hC⟩ := hG (X :: l) hl'
  obtain ⟨C0, hC0⟩ := hG l hl
  have hmem : ∀ (k : KG ε) (s : ℝ), g * toMK k * NormedSpace.exp (s • X) ∈ UJset ε := fun k s =>
    mul_mem_UJ (mul_mem_UJ hg (toMK_mem_UJ k)) (exp_mem_UJ hXl s)
  have hhs : ∀ (k : KG ε) (s : ℝ), hs (g * toMK k * NormedSpace.exp (s • X)) = hs g := fun k s => by
    rw [← toMK_expK_real hX, mul_assoc, ← toMK_mul]
    exact ((hermitian_small_ball n ε).2 _ _ (toMK_mem_K _)).1
  have hem : Measurable e := hec.measurable
  have hbd : ∀ (l' : List (Mx n)) (C' : ℝ), (∀ h ∈ UJset ε, ‖F l' h‖ ≤ C' * (1 + hs h) ^ N) →
      ∀ (k : KG ε) (s : ℝ), ‖e k * F l' (g * toMK k * NormedSpace.exp (s • X))‖ ≤ M * (C' * (1 + hs g) ^ N) :=
    fun l' C' hC' k s => by
      rw [norm_mul]
      refine mul_le_mul (hM k trivial) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM k trivial))
      rw [← hhs k s]
      exact hC' _ (hmem k s)
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun k => e k * F l (g * toMK k * NormedSpace.exp (t • X))) (muK ε) :=
    fun t => (hem.mul (measurable_fam hD hf hF0 l hl g hg _ (exp_mem_UJ hXl t))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X)))
      (muK ε) := (hem.mul (measurable_fam hD hf hF0 (X :: l) hl' g hg _ (exp_mem_UJ hXl 0))).aestronglyMeasurable
  have hint : Integrable (fun k => e k * F l (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) (muK ε) :=
    Integrable.mono' (integrable_const (M * (C0 * (1 + hs g) ^ N))) (hmeasF 0) (ae_of_all _ fun k => hbd l C0 hC0 k 0)
  have hdif : ∀ (k : KG ε) (s : ℝ), HasDerivAt (fun t : ℝ => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
      (e k * F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s := fun k s => by
    have h1 := hD l hl X hXl _ (hmem k s)
    have h2 : HasDerivAt (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)))
        (F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s :=
      HasDerivAt.comp_sub_const (f := fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp (t • X)))
        s s (by rw [sub_self]; exact h1)
    have e2 : (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X))) =
        fun t => F l (g * toMK k * NormedSpace.exp (t • X)) := by
      funext t
      rw [mul_assoc (g * toMK k), ← exp_add_smul, add_sub_cancel]
    rw [e2] at h2
    exact h2.const_mul (e k)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
    (F' := fun t k => e k * F (X :: l) (g * toMK k * NormedSpace.exp (t • X)))
    (bound := fun _ => M * (C * (1 + hs g) ^ N)) (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeasF) hint hmeasF'
    (ae_of_all _ fun k t _ => hbd (X :: l) C hC k t) (integrable_const _) (ae_of_all _ fun k s _ => hdif k s)
  have e3 : (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) =
      fun k => e k * F (X :: l) (g * toMK k) := by
    funext k
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  simpa only [e3] using key.2

theorem rder_avgK_all (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {y : Mx n} (hy : y ∈ UJset ε) :
    ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ k' : KG ε,
      rder ε u (avgK ε e f y) k' = ∫ k, e k * F u (y * toMK k' * toMK k) ∂(muK ε) := by
  intro u
  induction u with
  | nil =>
    intro _ k'
    rw [rder_nil]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hF0 _ (mul_mem_UJ (mul_mem_UJ hy (toMK_mem_UJ k')) (toMK_mem_UJ k))]
  | cons X l ih =>
    intro hu k'
    have hX : inK ε X := hu X List.mem_cons_self
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hlK Y hY).1
    rw [rder_cons]
    have e1 : (fun t : ℝ => rder ε l (avgK ε e f y) (k' * expK ε X t)) =
        fun t => ∫ k, e k * F l (y * toMK k' * toMK (expK ε X t) * toMK k) ∂(muK ε) := by
      funext t
      rw [ih hlK, toMK_mul, mul_assoc y]
    rw [e1]
    exact (hasDerivAt_avg hD hG hf hF0 hec he hl hX (mul_mem_UJ hy (toMK_mem_UJ k'))).deriv

theorem rder_avgK_one (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) (hD : IsDerFam ε F)
    (hG : FamGrowth ε N F) (f : Mx n → ℂ) (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g)
    (e : KG ε → ℂ) (hec : Continuous e) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) (u : List (Mx n))
    (hu : ∀ X ∈ u, inK ε X) (y : Mx n) (hy : y ∈ UJset ε) :
    GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  rw [rder_avgK_all hD hG hf hF0 hec he hy u hu 1, toMK_one, mul_one]

end GlobalTheory.KAvgDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → (∀ g ∈ UJset ε, F [] g = f g) → ∀ e : KG ε → ℂ, Continuous e → (∀ a k : KG ε, e (a * k * a⁻¹) = e k) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  first | exact @GlobalTheory.KAvgDeriv.rder_avgK_one | exact GlobalTheory.KAvgDeriv.rder_avgK_one | (intros; apply GlobalTheory.KAvgDeriv.rder_avgK_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section MatrixExtension

open scoped Matrix.Norms.Operator

def mxDer (X : Mx n) (F : Mx n → ℂ) : Mx n → ℂ := fun M => fderiv ℝ F M (M * X)

def mxDerW (l : List (Mx n)) (F : Mx n → ℂ) : Mx n → ℂ :=
  l.foldr (fun X G => mxDer X G) F

theorem contDiff_mxDer (X : Mx n) {F : Mx n → ℂ} (hF : ContDiff ℝ ⊤ F) : ContDiff ℝ ⊤ (mxDer X F) := by
  unfold mxDer
  exact (hF.fderiv_right le_top).clm_apply (contDiff_id.mul contDiff_const)

theorem contDiff_mxDerW (l : List (Mx n)) {F : Mx n → ℂ} (hF : ContDiff ℝ ⊤ F) :
    ContDiff ℝ ⊤ (mxDerW l F) := by
  induction l with
  | nil => exact hF
  | cons X l ih => exact contDiff_mxDer X ih

theorem hasDerivAt_exp_ofReal_smul (X : Mx n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun t : ℝ => NormedSpace.exp (t • X) := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h

theorem rder_eq_mxDerW {ε : Fin n → Bool} (l : List (Mx n)) (hl : ∀ X ∈ l, inK ε X) {F : Mx n → ℂ}
    (hF : ContDiff ℝ ⊤ F) {φ : KG ε → ℂ} (hφ : ∀ k, φ k = F (toMK k)) (k : KG ε) :
    rder ε l φ k = mxDerW l F (toMK k) := by
  induction l generalizing k with
  | nil => exact hφ k
  | cons X l ih =>
    have hX : inK ε X := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, inK ε Y := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    rw [rder_cons]
    have e : (fun t : ℝ => rder ε l φ (k * expK ε X t)) =
        (mxDerW l F) ∘ (fun t : ℝ => toMK k * NormedSpace.exp ((t : ℂ) • X)) := by
      funext t
      simp only [Function.comp, ih hl' (k * expK ε X t), toMK_mul, toMK_expK hX]
    rw [e]
    have hd : HasDerivAt (fun t : ℝ => toMK k * NormedSpace.exp ((t : ℂ) • X)) (toMK k * X) 0 :=
      (hasDerivAt_exp_ofReal_smul X).const_mul (toMK k)
    have hF' := ((contDiff_mxDerW l hF).differentiable (by simp)) (toMK k)
    have h2 := hF'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd (by simp [NormedSpace.exp_zero])
    rw [h2.deriv]
    rfl

def mxCoord (c : Fin n × Fin n × Bool) (M : Mx n) : ℂ :=
  if c.2.2 then M c.1 c.2.1 else star (M c.1 c.2.1)

theorem contDiff_mxCoord (c : Fin n × Fin n × Bool) : ContDiff ℝ ⊤ (mxCoord (n := n) c) := by
  let L : Mx n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c.1 c.2.1)
  have hL : ContDiff ℝ ⊤ fun M : Mx n => M c.1 c.2.1 := L.contDiff
  unfold mxCoord
  split_ifs
  · exact hL
  · exact (Complex.conjCLE.contDiff.comp hL : _)

theorem exists_ext_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    ∃ F : Mx n → ℂ, ContDiff ℝ ⊤ F ∧ ∀ k, φ k = F (toMK k) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    refine ⟨fun M => (s.map fun c => mxCoord c M).prod, ?_, fun k => rfl⟩
    induction s with
    | nil => simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Mx n => (1 : ℂ))
    | cons c s ih => simpa using (contDiff_mxCoord c).mul ih
  | zero => exact ⟨0, contDiff_const, fun k => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    exact ⟨F + G, hF.add hG, fun k => by simp [e, e']⟩
  | smul a x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    exact ⟨a • F, hF.const_smul a, fun k => by simp [e]⟩

theorem mxDer_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (b : ι → Mx n) (F : Mx n → ℂ) (M : Mx n) :
    mxDer (∑ j ∈ s, c j • b j) F M = ∑ j ∈ s, c j • mxDer (b j) F M := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mxDer, Matrix.mul_sum, Matrix.mul_smul, map_sum, map_smul]

theorem mxDer_sum (X : Mx n) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (G : ι → Mx n → ℂ)
    (hG : ∀ i ∈ s, ContDiff ℝ ⊤ (G i)) :
    mxDer X (fun M => ∑ i ∈ s, c i • G i M) = fun M => ∑ i ∈ s, c i • mxDer X (G i) M := by
  funext M
  have h : HasFDerivAt (fun M => ∑ i ∈ s, c i • G i M) (∑ i ∈ s, c i • fderiv ℝ (G i) M) M :=
    HasFDerivAt.fun_sum fun i hi => ((((hG i hi).differentiable (by simp)) M).hasFDerivAt).const_smul (c i)
  simp only [mxDer, h.fderiv, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]

end MatrixExtension

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section Expansion

open scoped Matrix.Norms.Operator

theorem mxDerW_expand {r : ℕ} (b : Fin r → Mx n) (cf : Mx n → Fin r → ℝ) {F : Mx n → ℂ}
    (hF : ContDiff ℝ ⊤ F) : ∀ (k : ℕ) (x : Fin k → Mx n), (∀ i, x i = ∑ j, cf (x i) j • b j) →
    mxDerW (List.ofFn x) F = fun M => ∑ σ : Fin k → Fin r,
      (∏ i, cf (x i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F M := by
  intro k
  induction k with
  | zero =>
    intro x _
    funext M
    simp
  | succ k ih =>
    intro x hx
    have ih' := ih (fun i => x i.succ) (fun i => hx i.succ)
    funext M
    rw [List.ofFn_succ]
    show mxDer (x 0) (mxDerW (List.ofFn fun i => x i.succ) F) M = _
    rw [ih', mxDer_sum (x 0) Finset.univ _ _ (fun σ _ => contDiff_mxDerW _ hF)]
    rw [← (Fin.consEquiv fun _ => Fin r).sum_comp, Fintype.sum_prod_type]
    have hx0 := hx 0
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have key : ∀ G, mxDer (x 0) G M = ∑ j, cf (x 0) j • mxDer (b j) G M := fun G => by
      conv_lhs => rw [hx0]
      exact mxDer_sum_smul _ _ _ _ _
    rw [key, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_comm]
    rfl

end Expansion

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section Basis

def kSub (ε : Fin n → Bool) : Submodule ℝ (Mx n) where
  carrier := {X | inK ε X}
  zero_mem' := by
    show inG ε 0 ∧ (0 : Mx n) * Jm ε = Jm ε * 0
    refine ⟨?_, by simp⟩
    show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  add_mem' := by
    intro X Y hX hY
    obtain ⟨hX1, hX2⟩ := hX
    obtain ⟨hY1, hY2⟩ := hY
    refine ⟨?_, ?_⟩
    · show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
      have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX1
      have h2 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY1
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
          = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
        _ = 0 := by rw [h1, h2, add_zero]
    · rw [Matrix.add_mul, Matrix.mul_add, hX2, hY2]
  smul_mem' := by
    intro c X hX
    obtain ⟨hX1, hX2⟩ := hX
    refine ⟨?_, ?_⟩
    · show (c • X)ᴴ * Jm ε + Jm ε * (c • X) = 0
      have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX1
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
        smul_zero]
    · show (c • X) * Jm ε = Jm ε * (c • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hX2]

theorem norm_entry_le_of_hs {X : Mx n} (h : hs X ≤ 1) (i j : Fin n) : ‖X i j‖ ≤ 1 := by
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ j', ‖X i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖X i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖X i j'‖ ^ 2 ≤ hs X :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖X i' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (X i j)]

theorem eq_sum_re_im (X : Mx n) :
    X = ∑ a : Fin n, ∑ b : Fin n, ((X a b).re • (Matrix.single a b (1 : ℂ) : Mx n) +
      (X a b).im • (Matrix.single a b Complex.I : Mx n)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, mul_one]
  exact (Complex.re_add_im _).symm

theorem abs_linear_le (ψ : Mx n →ₗ[ℝ] ℝ) {X : Mx n} (h : hs X ≤ 1) :
    |ψ X| ≤ ∑ a : Fin n, ∑ b : Fin n, (|ψ (Matrix.single a b (1 : ℂ))| + |ψ (Matrix.single a b Complex.I)|) := by
  conv_lhs => rw [eq_sum_re_im X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_smul, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 := norm_entry_le_of_hs h a b
  have hre : |(X a b).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h1
  have him : |(X a b).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h1
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have := abs_nonneg (ψ (Matrix.single a b (1 : ℂ)))
  have := abs_nonneg (ψ (Matrix.single a b Complex.I))
  nlinarith [abs_nonneg (X a b).re, abs_nonneg (X a b).im]

theorem exists_basis_kSub (ε : Fin n → Bool) : ∃ (r : ℕ) (b : Fin r → Mx n) (cf : Mx n → Fin r → ℝ) (A : ℝ),
    0 ≤ A ∧ (∀ j, inK ε (b j)) ∧ (∀ X, inK ε X → X = ∑ j, cf X j • b j) ∧
      (∀ X, inK ε X → hs X ≤ 1 → ∀ j, |cf X j| ≤ A) := by
  let B := Module.finBasis ℝ (kSub ε)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (kSub ε).subtype (Submodule.ker_subtype _)
  let ψ : Fin (Module.finrank ℝ (kSub ε)) → (Mx n →ₗ[ℝ] ℝ) := fun j => (B.coord j).comp g
  let A : ℝ := ∑ j, ∑ a : Fin n, ∑ b : Fin n,
    (|ψ j (Matrix.single a b (1 : ℂ))| + |ψ j (Matrix.single a b Complex.I)|)
  have hg' : ∀ X (hX : inK ε X), g X = ⟨X, hX⟩ := fun X hX =>
    LinearMap.congr_fun hg ⟨X, hX⟩
  refine ⟨Module.finrank ℝ (kSub ε), fun j => (B j : Mx n), fun X j => ψ j X, A, ?_, fun j => (B j).2, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro X hX
    have := congrArg Subtype.val (B.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at this
    simpa [ψ, hg' X hX] using this.symm
  · intro X _ h1 j
    refine (abs_linear_le (ψ j) h1).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ a : Fin n, ∑ b : Fin n,
      (|ψ j (Matrix.single a b (1 : ℂ))| + |ψ j (Matrix.single a b Complex.I)|))
      (fun j _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)

end Basis

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

theorem rder_bound_basisWords : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ),
    0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d →
      ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) →
        ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  intro n ε m
  obtain ⟨r, b, cf, A, hA, hb, hrep, hcf⟩ := exists_basis_kSub ε
  let word : ∀ k, (Fin k → Fin r) → List (Mx n) := fun k σ => List.ofFn fun i => b (σ i)
  let U : List (List (Mx n)) := (List.range (m + 1)).flatMap fun k =>
    (Finset.univ : Finset (Fin k → Fin r)).toList.map (word k)
  have hword : ∀ k σ, ∀ X ∈ word k σ, inK ε X := by
    intro k σ X hX
    simp only [word, List.mem_ofFn] at hX
    obtain ⟨i, rfl⟩ := hX
    exact hb _
  refine ⟨U, (max 1 A) ^ m, by positivity, ?_, ?_⟩
  · intro u hu X hX
    simp only [U, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨k, -, σ, -, rfl⟩ := hu
    exact hword k σ X hX
  · intro d φ hφ w hw hwK
    obtain ⟨F, hF, hφF⟩ := exists_ext_of_mem hφ
    have hx : ∀ i : Fin w.length, w.get i = ∑ j, cf (w.get i) j • b j := fun i =>
      hrep _ (hwK _ (List.get_mem w i)).1
    have e1 : rder ε w φ 1 = mxDerW w F (toMK 1) :=
      rder_eq_mxDerW w (fun X hX => (hwK X hX).1) hF hφF 1
    have e2 := mxDerW_expand b cf hF w.length w.get hx
    rw [List.ofFn_get] at e2
    have e3 : ∀ k (σ : Fin k → Fin r), mxDerW (word k σ) F (toMK 1) = rder ε (word k σ) φ 1 :=
      fun k σ => (rder_eq_mxDerW _ (hword k σ) hF hφF 1).symm
    have hcoef : ∀ σ : Fin w.length → Fin r, |∏ i, cf (w.get i) (σ i)| ≤ (max 1 A) ^ m := by
      intro σ
      rw [Finset.abs_prod]
      calc ∏ i, |cf (w.get i) (σ i)| ≤ ∏ _i : Fin w.length, max 1 A :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ =>
              (hcf _ (hwK _ (List.get_mem w i)).1 (hwK _ (List.get_mem w i)).2 _).trans (le_max_right _ _)
        _ = (max 1 A) ^ w.length := by simp
        _ ≤ (max 1 A) ^ m := pow_le_pow_right₀ (le_max_left _ _) hw
    have hsum : ∑ σ : Fin w.length → Fin r, ‖rder ε (word w.length σ) φ 1‖ ≤
        (U.map fun u => ‖rder ε u φ 1‖).sum := by
      have e4 : (U.map fun u => ‖rder ε u φ 1‖).sum = ((List.range (m + 1)).map fun k =>
          ∑ σ : Fin k → Fin r, ‖rder ε (word k σ) φ 1‖).sum := by
        simp only [U, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
        congr 1
        refine List.map_congr_left fun k _ => ?_
        show ((List.map (word k) Finset.univ.toList).map fun u => ‖rder ε u φ 1‖).sum = _
        rw [List.map_map, Finset.sum_map_toList]
        rfl
      rw [e4]
      exact List.single_le_sum (fun x hx => by
          obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
          exact Finset.sum_nonneg fun _ _ => norm_nonneg _) _
        (List.mem_map.2 ⟨w.length, List.mem_range.2 (by omega), rfl⟩)
    rw [e1, e2]
    calc ‖∑ σ : Fin w.length → Fin r, (∏ i, cf (w.get i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F (toMK 1)‖
        ≤ ∑ σ : Fin w.length → Fin r, ‖(∏ i, cf (w.get i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F (toMK 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ σ : Fin w.length → Fin r, (max 1 A) ^ m * ‖rder ε (word w.length σ) φ 1‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have := e3 w.length σ
          simp only [word] at this
          rw [this]
          exact mul_le_mul_of_nonneg_right (hcoef σ) (norm_nonneg _)
      _ = (max 1 A) ^ m * ∑ σ : Fin w.length → Fin r, ‖rder ε (word w.length σ) φ 1‖ := by
          rw [Finset.mul_sum]
      _ ≤ (max 1 A) ^ m * (U.map fun u => ‖rder ε u φ 1‖).sum :=
          mul_le_mul_of_nonneg_left hsum (by positivity)

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDeriv_norm_le_finite_words_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ), 0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) → ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  first | exact @GlobalTheory.KFourier.rder_bound_basisWords | exact GlobalTheory.KFourier.rder_bound_basisWords | (intros; apply GlobalTheory.KFourier.rder_bound_basisWords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryReal
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem coord_mul_eq_sum (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (a k : KG ε) :
    coord ε c (a * k) = ∑ l : Fin n, coord ε (c.1, l, c.2.2) a * coord ε (l, c.2.1, c.2.2) k := by
  simp only [coord, toMK_mul, Matrix.mul_apply]
  split_ifs
  · rfl
  · rw [star_sum]; exact Finset.sum_congr rfl fun l _ => by rw [star_mul', mul_comm]

theorem integrable_muK_of_continuous {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem conv_mono_mem (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) :
    ∀ (d : ℕ), s.length ≤ d → ∀ h : KG ε → ℂ, Continuous h →
      (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction s with
  | nil =>
    intro d _ h _
    simpa [mono] using const_mem ε d (∫ k, h k ∂(muK ε))
  | cons c s ih =>
    intro d hd h hh
    have hd' : s.length + 1 ≤ d := by simpa using hd
    have e : (fun k' : KG ε => ∫ k, mono ε (c :: s) (k'⁻¹ * k) * h k ∂(muK ε)) =
        ∑ l : Fin n, (fun k' : KG ε => coord ε (c.1, l, c.2.2) k'⁻¹) *
          (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * (coord ε (l, c.2.1, c.2.2) k * h k) ∂(muK ε)) := by
      funext k'
      simp only [Finset.sum_apply, Pi.mul_apply]
      simp only [← integral_const_mul]
      rw [← integral_finsetSum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h1 : mono ε (c :: s) (k'⁻¹ * k) = coord ε c (k'⁻¹ * k) * mono ε s (k'⁻¹ * k) := by simp [mono]
        simp only [h1, coord_mul_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      · intro l _
        refine integrable_muK_of_continuous (continuous_const.mul ?_)
        exact ((continuous_mono ε s).comp (continuous_const.mul continuous_id)).mul
          ((continuous_coord ε _).mul hh)
    rw [e]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact polyV_mono ε (show 1 + (d - 1) ≤ d by omega)
      (mul_mem (coord_inv_mem ε _) (ih (d - 1) (by omega) _ ((continuous_coord ε _).mul hh)))

theorem conv_mem {ε : Fin n → Bool} {d : ℕ} {e : KG ε → ℂ} (he : e ∈ polyV ε d) {h : KG ε → ℂ}
    (hh : Continuous h) : (fun k' : KG ε => ∫ k, e (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact conv_mono_mem ε s d hs h hh
  | zero =>
    simpa using const_mem ε d 0
  | add x y hx hy ihx ihy =>
    convert add_mem ihx ihy using 1
    funext k'
    simp only [Pi.add_apply, add_mul]
    refine integral_add (integrable_muK_of_continuous ?_) (integrable_muK_of_continuous ?_)
    · exact ((continuous_of_mem (d := d) hx).comp (continuous_const.mul continuous_id)).mul hh
    · exact ((continuous_of_mem (d := d) hy).comp (continuous_const.mul continuous_id)).mul hh
  | smul a x _ ih =>
    convert Submodule.smul_mem _ a ih using 1
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem avgK_mem : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i →
    ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε,
      GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  intro n ε i e he f hf y hy
  have hh : Continuous fun k : KG ε => f (y * toMK k) :=
    hf.comp_continuous (continuous_const.mul (GlobalTheory.TypeSum.continuous_toMK ε))
      fun k => GlobalTheory.TypeSum.mul_mem_UJ hy (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))
  convert conv_mem he hh using 1
  funext k'
  rw [← integral_mul_left_eq_self (μ := muK ε) _ k']
  simp only [avgK, inv_mul_cancel_left, toMK_mul, Matrix.mul_assoc]

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryAverage_mem_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  first | exact @GlobalTheory.KFourier.avgK_mem | exact GlobalTheory.KFourier.avgK_mem | (intros; apply GlobalTheory.KFourier.avgK_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier
open MeasureTheory Matrix Formalism.REAL GlobalTheory.TypeSum

variable {n : ℕ}

theorem rder_mem (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d) (l : List (Mx n))
    (hl : ∀ X ∈ l, inK ε X) : rder ε l φ ∈ polyV ε d := by
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    have h := (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε d _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)).1
    exact h

theorem hs_mul_toMK (ε : Fin n → Bool) (y : Mx n) (k : KG ε) : hs (y * toMK k) = hs y :=
  ((hermitian_small_ball n ε).2 y _ k.2).1

theorem toMK_expK_mul (ε : Fin n → Bool) (X : Mx n) (hK : inK ε X) (t : ℝ) (x : KG ε) :
    toMK (expK ε X t * x) = NormedSpace.exp (t • X) * toMK x := by
  rw [toMK_mul, toMK_expK hK, Complex.coe_smul]

theorem summable_listSum {ι : Type} (U : List ι) (b : ι → ℕ → ℝ) (hb : ∀ u ∈ U, Summable (b u)) :
    Summable fun i => (U.map fun u => b u i).sum := by
  induction U with
  | nil => simp
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hb u List.mem_cons_self).add (ih fun v hv => hb v (List.mem_cons_of_mem _ hv))

theorem exists_rightKFourier : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  intro n ε
  have hker : ∀ i, IsKer ε i (kerE ε i) := fun i => isKer_kerE (GlobalTheory.T.exists_compactUnitary_fourierKernel ε i)
  refine ⟨kerE ε, fun i => continuous_of_mem (hker i).1, fun i => kFinFun_of_mem (hker i).1, ?_⟩
  intro f hf hU
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  have hcF : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hdec : ∀ u : List (Mx n), ∃ b : ℕ → ℝ, Summable b ∧ ((∀ X ∈ u, inK ε X) → ∀ i, ∀ y ∈ UJset ε,
      ‖∫ k, kerE ε i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N) := by
    intro u
    by_cases hu : ∀ X ∈ u, inK ε X
    · obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.kFourier_coefficient_rapid_decay ε N F hFd hFg hcF (kerE ε) hker u hu
      exact ⟨b, hb, fun _ => hb'⟩
    · exact ⟨0, summable_zero, fun h => absurd h hu⟩
  choose b hbs hbb using hdec
  choose U C hC0 hUK hC using GlobalTheory.T.rightDeriv_norm_le_finite_words_bound ε
  have hQ : ∀ i, ∀ y ∈ UJset ε, avgK ε (kerE ε i) f y ∈ polyV ε i := fun i y hy =>
    GlobalTheory.T.compactUnitaryAverage_mem_polyV ε i _ (hker i).1 f hf y hy
  have hbound : ∀ i m (w : List (Mx n)), w.length ≤ m → (∀ X ∈ w, X ∈ GlobalTheory.SmoothGlob.lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖rder ε w (avgK ε (kerE ε i) f y) 1‖ ≤ C m * ((U m).map fun u => b u i).sum * (1 + hs y) ^ N := by
    intro i m w hw hwX y hy
    have hwK : ∀ X ∈ w, inK ε X ∧ hs X ≤ 1 := fun X hX =>
      ⟨inK_of_skew (hwX X hX).1 (hwX X hX).2.1, (hwX X hX).2.2⟩
    have h1 := hC m i _ (hQ i y hy) w hw hwK
    have h2 : ((U m).map fun u => ‖rder ε u (avgK ε (kerE ε i) f y) 1‖).sum ≤
        ((U m).map fun u => b u i * (1 + hs y) ^ N).sum := by
      refine List.sum_le_sum fun u hu => ?_
      rw [GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq ε N F hFd hFg f hf hF0 _ (continuous_of_mem (hker i).1) (GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant ε i _ (hker i)) u (hUK m u hu) y hy]
      exact hbb u (hUK m u hu) i y hy
    rw [List.sum_map_mul_right] at h2
    calc _ ≤ _ := h1
      _ ≤ C m * (((U m).map fun u => b u i).sum * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_left h2 (hC0 m)
      _ = _ := by ring
  refine ⟨N, fun i l y => rder ε l (avgK ε (kerE ε i) f y) 1,
    fun i m => C m * ((U m).map fun u => b u i).sum, ?_, ?_, hbound, ?_, ?_⟩
  · intro i y hy
    simp [avgK, toMK_one]
  · intro i l hl X hX hXs y hy
    have hK := inK_of_skew hX hXs
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => inK_of_skew (hl Y hY).1 (hl Y hY).2
    have hR := rder_mem ε i _ (hQ i y hy) l hlK
    have e1 : (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1) =
        fun t : ℝ => rder ε l (avgK ε (kerE ε i) f y) (1 * expK ε X t) := by
      funext t
      rw [one_mul, ← mul_one (expK ε X t), ← rder_left ε l _ (expK ε X t) 1]
      congr 1
      funext x
      unfold avgK
      rw [toMK_expK_mul ε X hK t x]
      simp only [Matrix.mul_assoc]
    show HasDerivAt (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1)
      (rder ε [X] (rder ε l (avgK ε (kerE ε i) f y)) 1) 0
    rw [e1]
    exact (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε i _ hR X hK).2 1
  · intro m
    exact (summable_listSum (U m) b fun u _ => hbs u).mul_left (C m)
  · intro y hy
    have key := GlobalTheory.T.hasSum_compactUnitaryFourier_value_one ε (kerE ε) hker (fun k => f (y * toMK k)) ?_ (fun i => C 0 * ((U 0).map fun u => b u i).sum * (1 + hs y) ^ N)
      (((summable_listSum (U 0) b fun u _ => hbs u).mul_left (C 0)).mul_right _) ?_
    · simpa [toMK_one] using key
    · exact hf.comp_continuous ((continuous_const.mul (continuous_toMK ε))) fun k => mul_mem_UJ hy (K_le_UJ k.2)
    · intro i k'
      have hyk : y * toMK k' ∈ UJset ε := mul_mem_UJ hy (K_le_UJ k'.2)
      have := hbound i 0 [] le_rfl (by simp) _ hyk
      rw [hs_mul_toMK] at this
      simpa [avgK, toMK_one, toMK_mul, Matrix.mul_assoc] using this

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  first | exact @GlobalTheory.KFourier.exists_rightKFourier | exact GlobalTheory.KFourier.exists_rightKFourier | (intros; apply GlobalTheory.KFourier.exists_rightKFourier <;> assumption)
end
