module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGap
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirInverseTopDegreeBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBou
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBou
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier.CasimirMove

variable {n : ℕ}

theorem expK_add {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (s t : ℝ) :
    expK ε X (s + t) = expK ε X s * expK ε X t := by
  have hEG := group_exponential_facts n ε X hX.1
  have hEK := hEG.2.2.2 hX
  apply Subtype.ext
  show ((expK ε X (s + t) : KG ε) : UJ ε) = (expK ε X s : UJ ε) * (expK ε X t : UJ ε)
  rw [hEK.1, hEK.1, hEK.1]
  exact hEG.2.1 s t

theorem expK_zero {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) : expK ε X 0 = 1 := by
  have hEG := group_exponential_facts n ε X hX.1
  have hEK := hEG.2.2.2 hX
  apply Subtype.ext
  show ((expK ε X 0 : KG ε) : UJ ε) = 1
  rw [hEK.1]; exact hEG.1

theorem integral_deriv_eq_zero {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) {G D : KG ε → ℂ}
    (hG : Measurable G) (hD : Measurable D) (hGi : Integrable G (muK ε)) {C : ℝ} (hC : ∀ k, ‖D k‖ ≤ C)
    (hder : ∀ k, HasDerivAt (fun t : ℝ => G (k * expK ε X t)) (D k) 0) : ∫ k, D k ∂(muK ε) = 0 := by
  have hder' : ∀ k s, HasDerivAt (fun t => G (k * expK ε X t)) (D (k * expK ε X s)) s := by
    intro k s
    have h1 := hder (k * expK ε X s)
    have h2 : HasDerivAt (fun t => G (k * expK ε X s * expK ε X (t - s))) (D (k * expK ε X s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => G (k * expK ε X s * expK ε X t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => G (k * expK ε X s * expK ε X (t - s))) = fun t => G (k * expK ε X t) := by
      funext t
      rw [mul_assoc, ← expK_add hX, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (𝕜 := ℝ)
    (F := fun t k => G (k * expK ε X t)) (F' := fun t k => D (k * expK ε X t)) (x₀ := 0) (bound := fun _ => C)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hG.comp (measurable_mul_const _)).aestronglyMeasurable)
    (by simpa only [expK_zero hX, mul_one] using hGi)
    (hD.comp (measurable_mul_const _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k t _ => hC _) (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hder' k t)).2
  simp only [integral_mul_right_eq_self (μ := muK ε) G, expK_zero hX, mul_one] at h
  exact h.unique (hasDerivAt_const _ _)

theorem measurable_of_deriv {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) {G D : KG ε → ℂ}
    (hG : Measurable G) (hder : ∀ k, HasDerivAt (fun t : ℝ => G (k * expK ε X t)) (D k) 0) : Measurable D := by
  have hlim : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun m => ?_⟩
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    exact this.ne'
  refine measurable_of_tendsto_metrizable
    (f := fun (m : ℕ) k => slope (fun t : ℝ => G (k * expK ε X t)) 0 (1 / ((m : ℝ) + 1))) (fun m => ?_) ?_
  · simp only [slope_def_module, expK_zero hX, mul_one]
    exact ((hG.comp (measurable_mul_const _)).sub hG).const_smul _
  · exact tendsto_pi_nhds.2 fun k => (hasDerivAt_iff_tendsto_slope.1 (hder k)).comp hlim

theorem hasDerivAt_fam {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {X : Mx n} (hX : inK ε X) {y : Mx n} (hy : y ∈ UJset ε) (k : KG ε) :
    HasDerivAt (fun t : ℝ => F w (y * toMK (k * expK ε X t))) (F (X :: w) (y * toMK k)) 0 := by
  have h := hF w (fun Y hY => (hw Y hY).1) X hX.1 (y * toMK k) (mul_mem_UJ hy (K_le_UJ (toMK_mem_K k)))
  simpa only [toMK_mul, toMK_expK hX, Complex.coe_smul, Matrix.mul_assoc] using h

theorem measurable_fam {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)} (hw : ∀ Y ∈ w, inK ε Y) :
    Measurable fun k : KG ε => F w (y * toMK k) := by
  induction w with
  | nil =>
    exact (hc.comp_continuous (continuous_const.mul (continuous_toMK ε))
      fun k => mul_mem_UJ hy (K_le_UJ (toMK_mem_K k))).measurable
  | cons X w ih =>
    have hw' := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hX := hw X List.mem_cons_self
    exact measurable_of_deriv hX (ih hw') (hasDerivAt_fam hF hw' hX hy)

theorem bound_fam {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hg : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, inK ε Y) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ∀ k : KG ε, ‖F w (y * toMK k)‖ ≤ C * (1 + hs y) ^ N := by
  obtain ⟨C, hC⟩ := hg w fun Y hY => (hw Y hY).1
  refine ⟨C, fun y hy k => ?_⟩
  have h := hC _ (mul_mem_UJ hy (K_le_UJ (toMK_mem_K k)))
  rwa [((hermitian_small_ball n ε).2 _ _ (toMK_mem_K k)).1] at h

theorem integrable_mul_fam {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hg : FamGrowth ε N F) (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {p : KG ε → ℂ} (hp : Continuous p) :
    Integrable (fun k => p k * F w (y * toMK k)) (muK ε) := by
  obtain ⟨C, hC⟩ := bound_fam hg hw
  exact (integrable_of_continuousK hp).mul_bdd (measurable_fam hF hc hy hw).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC y hy))

theorem by_parts {ε : Fin n → Bool} {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F)
    (hg : FamGrowth ε N F) (hc : ContinuousOn (F []) (UJset ε)) {y : Mx n} (hy : y ∈ UJset ε) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, inK ε Y) {X : Mx n} (hX : inK ε X) {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) :
    ∫ k, rder ε [X] p k * F w (y * toMK k) ∂(muK ε) = -∫ k, p k * F (X :: w) (y * toMK k) ∂(muK ε) := by
  have hw' : ∀ Y ∈ X :: w, inK ε Y := fun Y hY => (List.mem_cons.1 hY).elim (fun e => e ▸ hX) (hw Y)
  obtain ⟨hq, hd⟩ := rder_mem_and_hasDerivAt ε d p hp X hX
  have cp := continuous_of_mem hp
  have cq := continuous_of_mem hq
  obtain ⟨C₁, h₁⟩ := bound_fam hg hw
  obtain ⟨C₂, h₂⟩ := bound_fam hg hw'
  obtain ⟨B₁, b₁⟩ := isCompact_univ.exists_bound_of_continuousOn cq.continuousOn
  obtain ⟨B₂, b₂⟩ := isCompact_univ.exists_bound_of_continuousOn cp.continuousOn
  have key := integral_deriv_eq_zero hX (G := fun k => p k * F w (y * toMK k))
    (D := fun k => rder ε [X] p k * F w (y * toMK k) + p k * F (X :: w) (y * toMK k))
    (cp.measurable.mul (measurable_fam hF hc hy hw))
    ((cq.measurable.mul (measurable_fam hF hc hy hw)).add (cp.measurable.mul (measurable_fam hF hc hy hw')))
    (integrable_mul_fam hF hg hc hy hw cp) (C := B₁ * (C₁ * (1 + hs y) ^ N) + B₂ * (C₂ * (1 + hs y) ^ N))
    (fun k => (norm_add_le _ _).trans (add_le_add
      (norm_mul_le_of_le (b₁ k trivial) (h₁ y hy k)) (norm_mul_le_of_le (b₂ k trivial) (h₂ y hy k))))
    (fun k => by
      have h := (hd k).fun_mul (hasDerivAt_fam hF hw hX hy k)
      simpa only [expK_zero hX, mul_one] using h)
  rw [integral_add (integrable_mul_fam hF hg hc hy hw cq) (integrable_mul_fam hF hg hc hy hw' cp)] at key
  exact eq_neg_of_add_eq_zero_left key

theorem integral_norm_le_sqrt {ε : Fin n → Bool} {p : KG ε → ℂ} (hp : Continuous p) :
    ∫ k, ‖p k‖ ∂(muK ε) ≤ Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  have i1 : Integrable (fun k => ‖p k‖) (muK ε) := (integrable_of_continuousK hp).norm
  have i2 : Integrable (fun k => ‖p k‖ ^ 2) (muK ε) :=
    (hp.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set a := ∫ k, ‖p k‖ ∂(muK ε) with ha
  have h0 : 0 ≤ ∫ k, (‖p k‖ ^ 2 - 2 * a * ‖p k‖ + a ^ 2) ∂(muK ε) :=
    integral_nonneg fun k => by
      have := sq_nonneg (‖p k‖ - a)
      simp only [Pi.zero_apply]
      nlinarith
  rw [integral_add (f := fun k => ‖p k‖ ^ 2 - 2 * a * ‖p k‖) (i2.sub (i1.const_mul _)) (integrable_const _), integral_sub i2 (i1.const_mul _),
    integral_const_mul, integral_const, ← ha] at h0
  simp only [probReal_univ, smul_eq_mul, one_mul] at h0
  exact Real.le_sqrt_of_sq_le (by nlinarith)

theorem casimir_mem {ε : Fin n → Bool} {r : ℕ} {X : Fin r → Mx n} (hX : ∀ j, inK ε (X j)) {d : ℕ}
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : (∑ j, rder ε [X j, X j] p) ∈ polyV ε d :=
  Submodule.sum_mem _ fun j _ =>
    (rder_mem_and_hasDerivAt ε d _ (rder_mem_and_hasDerivAt ε d p hp _ (hX j)).1 _ (hX j)).1

theorem casimir_pow_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (M : ℕ) (u : List (Mx n)), (∀ Y ∈ u, inK ε Y) → ∃ C : ℝ, ∀ (d : ℕ) (p : KG ε → ℂ), p ∈ polyV ε d → ∀ y ∈ UJset ε, ‖∫ k, ((fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p) k * F u (y * toMK k) ∂(muK ε)‖ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  intro n ε N F hF hg hc r X hX M
  induction M with
  | zero =>
    intro u hu
    obtain ⟨C, hC⟩ := bound_fam hg hu
    refine ⟨C, fun d p hp y hy => ?_⟩
    have cp := continuous_of_mem hp
    have h0 : 0 ≤ C * (1 + hs y) ^ N := (norm_nonneg _).trans (hC y hy 1)
    calc _ ≤ ∫ k, C * (1 + hs y) ^ N * ‖p k‖ ∂(muK ε) :=
          norm_integral_le_of_norm_le ((integrable_of_continuousK cp).norm.const_mul _)
            (Filter.Eventually.of_forall fun k => by
              rw [mul_comm (C * _)]
              exact norm_mul_le_of_le le_rfl (hC y hy k))
      _ ≤ _ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_norm_le_sqrt cp) h0
  | succ M ih =>
    intro u hu
    have h1 : ∀ j, ∀ Y ∈ X j :: u, inK ε Y := fun j Y hY => (List.mem_cons.1 hY).elim (fun e => e ▸ hX j) (hu Y)
    have h2 : ∀ j, ∀ Y ∈ X j :: X j :: u, inK ε Y := fun j Y hY =>
      (List.mem_cons.1 hY).elim (fun e => e ▸ hX j) (h1 j Y)
    choose C hC using fun j => ih _ (h2 j)
    refine ⟨∑ j, C j, fun d p hp y hy => ?_⟩
    have hq : (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p ∈ polyV ε d :=
      Function.Iterate.rec (fun φ => φ ∈ polyV ε d) hp (fun _ h => casimir_mem hX h) M
    rw [Function.iterate_succ_apply']
    set q := (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p with hqd
    have hr : ∀ j, rder ε [X j] q ∈ polyV ε d := fun j => (rder_mem_and_hasDerivAt ε d q hq _ (hX j)).1
    have hrr : ∀ j, rder ε [X j, X j] q ∈ polyV ε d := fun j => (rder_mem_and_hasDerivAt ε d _ (hr j) _ (hX j)).1
    have e : ∀ j, ∫ k, rder ε [X j, X j] q k * F u (y * toMK k) ∂(muK ε) =
        ∫ k, q k * F (X j :: X j :: u) (y * toMK k) ∂(muK ε) := fun j => by
      have a := by_parts hF hg hc hy hu (hX j) (hr j)
      rw [by_parts hF hg hc hy (h1 j) (hX j) hq, neg_neg] at a
      exact a
    simp only [Finset.sum_apply, Finset.sum_mul]
    rw [integral_finsetSum _ fun j _ => integrable_mul_fam hF hg hc hy hu (continuous_of_mem (hrr j))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [e j]
    exact hC j d p hp y hy

end GlobalTheory.KFourier.CasimirMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBouStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (M : ℕ) (u : List (Mx n)), (∀ Y ∈ u, inK ε Y) → ∃ C : ℝ, ∀ (d : ℕ) (p : KG ε → ℂ), p ∈ polyV ε d → ∀ y ∈ UJset ε, ‖∫ k, ((fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p) k * F u (y * toMK k) ∂(muK ε)‖ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  first | exact @GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | exact GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | (intros; apply GlobalTheory.KFourier.CasimirMove.casimir_pow_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem integral_star_mul_self {ε : Fin n → Bool} (f : KG ε → ℂ) :
    ∫ k, star (f k) * f k ∂(muK ε) = ((∫ k, ‖f k‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1; funext k
  rw [mul_comm, ← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

def l2InnerCore {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) (hV : ∀ p ∈ V, Continuous p) :
    InnerProductSpace.Core ℂ V where
  inner p q := ∫ k, star (p.1 k) * q.1 k ∂(muK ε)
  conj_inner_symm p q := by
    rw [← integral_conj]
    congr 1; funext k
    simp [mul_comm]
  re_inner_nonneg p := by
    rw [integral_star_mul_self]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun k => by positivity
  add_left p q r := by
    have hp := hV _ p.2
    have hq := hV _ q.2
    have hr := hV _ r.2
    rw [← integral_add (integrable_of_continuousK (f := fun k => star (p.1 k) * r.1 k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q.1 k) * r.1 k) (by fun_prop))]
    congr 1; funext k
    simp [add_mul]
  smul_left p q c := by
    rw [← integral_const_mul]
    congr 1; funext k
    simp [mul_assoc]
  definite p h := by
    have hp := hV _ p.2
    have h0 : ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = 0 := by
      have h' : ∫ k, star (p.1 k) * p.1 k ∂(muK ε) = 0 := h
      rw [integral_star_mul_self] at h'
      exact_mod_cast h'
    have hns : Continuous (fun k => ‖p.1 k‖ ^ 2) := by fun_prop
    have h2 : (fun k => ‖p.1 k‖ ^ 2) =ᵐ[muK ε] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
        ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h0
    have h3 : (fun k => ‖p.1 k‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
    ext k
    simpa using congrFun h3 k

theorem exists_parseval {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ p ∈ V, Continuous p) :
    ∃ φ : Fin (Module.finrank ℂ V) → KG ε → ℂ, (∀ j, φ j ∈ V) ∧ (∀ j, ∫ k, ‖φ j k‖ ^ 2 ∂(muK ε) = 1) ∧
      ∀ r ∈ V, ∫ k, ‖r k‖ ^ 2 ∂(muK ε) = ∑ j, ‖∫ k, star (r k) * φ j k ∂(muK ε)‖ ^ 2 := by
  letI c := l2InnerCore V hV
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hin : ∀ p q : V, inner ℂ p q = ∫ k, star (p.1 k) * q.1 k ∂(muK ε) := fun _ _ => rfl
  have hn : ∀ p : V, ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = ‖p‖ ^ 2 := by
    intro p
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p
    rw [hin, integral_star_mul_self] at h
    apply Complex.ofReal_injective
    rw [h, Complex.ofReal_pow]
    rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨fun j => (b j).1, fun j => (b j).2, fun j => ?_, fun r hr => ?_⟩
  · rw [hn, b.orthonormal.1 j, one_pow]
  · rw [hn ⟨r, hr⟩, ← b.sum_sq_norm_inner_left]
    rfl

theorem mul_left_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact mul_left_mem a h

def topV (ε : Fin n → Bool) (i : ℕ) : Submodule ℂ (KG ε → ℂ) where
  carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, fun q hq => ?_⟩
    have h1 := continuous_of_mem ha
    have h2 := continuous_of_mem hb
    have h3 := continuous_of_mem (lowV_le ε i hq)
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integrable_of_continuousK (f := fun k => star (q k) * a k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q k) * b k) (by fun_prop)), ha' q hq, hb' q hq, add_zero]
  zero_mem' := ⟨zero_mem _, fun q _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
    have : (fun k => star (q k) * (c • a) k) = fun k => c * (star (q k) * a k) := by
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, integral_const_mul, ha' q hq, mul_zero]

theorem topV_le (ε : Fin n → Bool) (i : ℕ) : topV ε i ≤ polyV ε i := fun _ h => h.1

theorem mul_left_mem_top {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ topV ε i) :
    (fun k => φ (a * k)) ∈ topV ε i := by
  refine ⟨mul_left_mem a h.1, fun q hq => ?_⟩
  have h1 := h.2 _ (mul_left_mem_low a⁻¹ hq)
  rw [← integral_mul_left_eq_self (μ := muK ε) _ a] at h1
  simpa only [inv_mul_cancel_left] using h1

theorem star_mem_top {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) :
    (fun k => star (e k)) ∈ topV ε i := by
  refine ⟨star_mem he.1, fun q hq => ?_⟩
  calc ∫ k, star (q k) * star (e k) ∂(muK ε)
      = ∫ k, (starRingEnd ℂ) (e k * q k) ∂(muK ε) := by
        congr 1; funext k; rw [map_mul, mul_comm]; rfl
    _ = (starRingEnd ℂ) (∫ k, e k * q k ∂(muK ε)) := integral_conj
    _ = 0 := by rw [he.2.1 q hq, map_zero]

theorem integral_norm_sq_ker_le : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  intro n ε i e he
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : FiniteDimensional ℂ (topV ε i) := Submodule.finiteDimensional_of_le (topV_le ε i)
  obtain ⟨φ, hφ, h1, hP⟩ := exists_parseval (topV ε i) (fun p hp => continuous_of_mem hp.1)
  have key : ∀ a : KG ε, ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∑ j, ‖φ j a‖ ^ 2 := by
    intro a
    have h := hP _ (mul_left_mem_top a⁻¹ (star_mem_top he))
    simp only [star_star, norm_star] at h
    rw [integral_mul_left_eq_self (μ := muK ε) (fun k => ‖e k‖ ^ 2) a⁻¹] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := mul_left_mem_top a (hφ j)
    have h3 := he.2.2 _ h2.1 h2.2
    rw [← integral_mul_left_eq_self (μ := muK ε) _ a]
    simp only [inv_mul_cancel_left, mul_one] at h3 ⊢
    rw [h3]
  have hint : ∀ j, Integrable (fun a => ‖φ j a‖ ^ 2) (muK ε) := by
    intro j
    have hp := continuous_of_mem (hφ j).1
    have hns : Continuous (fun k => ‖φ j k‖ ^ 2) := by fun_prop
    exact (integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re
  calc ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∫ _a, (∫ k, ‖e k‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by simp
    _ = ∫ a, ∑ j, ‖φ j a‖ ^ 2 ∂(muK ε) := by congr 1; funext a; exact key a
    _ = ∑ j, ∫ a, ‖φ j a‖ ^ 2 ∂(muK ε) := integral_finsetSum _ fun j _ => hint j
    _ = (Module.finrank ℂ (topV ε i) : ℝ) := by simp [h1]
    _ ≤ _ := by exact_mod_cast Submodule.finrank_mono (topV_le ε i)

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e → ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  first | exact @GlobalTheory.KFourier.integral_norm_sq_ker_le | exact GlobalTheory.KFourier.integral_norm_sq_ker_le | (intros; apply GlobalTheory.KFourier.integral_norm_sq_ker_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankCompactUnitaryPolyFunDegLELe
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankCompactUnitaryPolyFunDegLELe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem mono_eq_prod_pow {n : ℕ} (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) (k : KG ε) :
    mono ε s k = ∏ c : Fin n × Fin n × Bool, coord ε c k ^ s.count c := by
  classical
  unfold mono
  rw [Finset.prod_list_map_count]
  have h := Finset.prod_subset (M := ℂ) (f := fun c => coord ε c k ^ s.count c) (Finset.subset_univ (s.toFinset))
    (fun c _ hc => by rw [List.count_eq_zero_of_not_mem (by simpa using hc), pow_zero])
  convert h using 4
  all_goals exact lawful_beq_subsingleton _ _

theorem finrank_polyV_le {n : ℕ} (ε : Fin n → Bool) (d : ℕ) :
    Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  classical
  let b : ((Fin n × Fin n × Bool) → Fin (d + 1)) → (KG ε → ℂ) :=
    fun f k => ∏ c : Fin n × Fin n × Bool, coord ε c k ^ (f c : ℕ)
  have hle : polyV ε d ≤ Submodule.span ℂ (Set.range b) := by
    rw [polyV_eq]
    refine Submodule.span_le.2 ?_
    rintro φ ⟨s, hs, rfl⟩
    refine Submodule.subset_span ⟨fun c => ⟨s.count c, Nat.lt_succ_of_le ((List.count_le_length).trans hs)⟩, ?_⟩
    funext k
    rw [mono_eq_prod_pow]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  calc Module.finrank ℂ (polyV ε d) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card ((Fin n × Fin n × Bool) → Fin (d + 1)) := finrank_range_le_card b
    _ = (d + 1) ^ (2 * n ^ 2) := by
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        ring

end GlobalTheory.KFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankCompactUnitaryPolyFunDegLELeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ), Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  first | exact @GlobalTheory.KFourier.finrank_polyV_le | exact GlobalTheory.KFourier.finrank_polyV_le | (intros; apply GlobalTheory.KFourier.finrank_polyV_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KSpan

def kSub {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | inK ε Y}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · unfold inG at *
      rw [conjTranspose_add, add_mul, mul_add]
      calc _ = (aᴴ * Jm ε + Jm ε * a) + (bᴴ * Jm ε + Jm ε * b) := by abel
        _ = 0 := by rw [ha1, hb1, add_zero]
    · rw [add_mul, mul_add, ha2, hb2]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp [inG]
    · simp
  smul_mem' := by
    intro t Z hZ
    have h := inK_smul_real ε hZ t
    rwa [Complex.coe_smul] at h

theorem finite_real_span : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  intro n ε
  let b := Module.finBasis ℝ (kSub ε)
  refine ⟨Module.finrank ℝ (kSub ε), fun j => ((b j : kSub ε) : Matrix (Fin n) (Fin n) ℂ), fun j => (b j).2, ?_⟩
  intro Y hY
  refine ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.coe_smul]

end GlobalTheory.KSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  first | exact @GlobalTheory.KSpan.finite_real_span | exact GlobalTheory.KSpan.finite_real_span | (intros; apply GlobalTheory.KSpan.finite_real_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory

theorem hs_nonneg' {n : ℕ} (y : Mx n) : 0 ≤ hs y := by
  show 0 ≤ ∑ i, ∑ j, ‖y i j‖ ^ 2
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem kFourier_coeff_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  intro n ε N F hD hG hC e he u hu
  obtain ⟨r, X, hX, hsp⟩ := GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra ε
  obtain ⟨c, α, hc, hα, hgap⟩ := GlobalTheory.T.compactUnitary_polynomial_spectral_gap ε X hX hsp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (n : ℝ) ^ 2 + 2 < α * M := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((n : ℝ) ^ 2 + 2) / α)
    exact ⟨M, by rw [div_lt_iff₀ hα] at hM; linarith⟩
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX 0 u hu
  obtain ⟨C, hCM⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX M u hu
  have hlnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((c * x ^ α) ^ M)⁻¹ := fun x hx =>
    inv_nonneg.mpr (pow_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hx _)) _)
  let B : ℕ → ℝ := fun i => |C| * ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)
  refine ⟨fun i => if i = 0 then |C0| * Real.sqrt (Module.finrank ℂ (polyV ε 0)) else B i, ?_, ?_⟩
  · refine (summable_nat_add_iff 1).mp ?_
    have hp : (n : ℝ) ^ 2 - α * M < -1 := by linarith
    have hsm : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ ((n : ℝ) ^ 2 - α * M)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsm.mul_left (|C| * (c ^ M)⁻¹ * 2 ^ (n ^ 2)))
    · simp only [Nat.add_one_ne_zero, if_false, B]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hlnn _ (Nat.cast_nonneg _))) (by positivity)
    · simp only [Nat.add_one_ne_zero, if_false, B]
      set x : ℝ := ((i + 1 : ℕ) : ℝ) with hx
      have hx1 : 1 ≤ x := by simp [hx]
      have hx0 : 0 < x := by linarith
      have e1 : (c * x ^ α) ^ M = c ^ M * x ^ (α * M) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      have e2 : (x + 1) ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2) := by
        rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have e3 : x ^ ((n : ℝ) ^ 2 - α * M) = x ^ ((n : ℝ) ^ 2) * (x ^ (α * M))⁻¹ := by
        rw [Real.rpow_sub hx0, div_eq_mul_inv]
      rw [e1, e3, mul_inv]
      have h0 : 0 ≤ |C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le _)))
          (inv_nonneg.mpr (Real.rpow_nonneg hx0.le _))
      calc |C| * ((c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2)
          = (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2) := by ring
        _ ≤ (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left e2 h0
        _ = _ := by ring
  · intro i y hy
    have hy0 : 0 ≤ (1 + hs y) ^ N := pow_nonneg (by linarith [hs_nonneg' y]) _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true]
      have h := hC0 0 (e 0) (he 0).1 y hy
      simp only [Function.iterate_zero, id] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε 0 (e 0) (he 0)
      calc _ ≤ C0 * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖e 0 k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C0| * (1 + hs y) ^ N * Real.sqrt (Module.finrank ℂ (polyV ε 0)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_le_sqrt hk)
              (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by ring
    · have hi0 : i ≠ 0 := hi.ne'
      simp only [hi0, if_false]
      have hl : 0 < c * (i : ℝ) ^ α := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)
      obtain ⟨s, hsP, hse, hsn⟩ := GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound ε X hX i (c * (i : ℝ) ^ α) hl
        (fun p hp hq => hgap i hi p hp hq) M (e i) (he i).1
        (fun q hq => by rw [← (he i).2.1 q hq]; congr 1; funext k; ring)
      have h := hCM i s hsP y hy
      rw [hse] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε i (e i) (he i)
      have hd : (Module.finrank ℂ (polyV ε i) : ℝ) ≤ ((i : ℝ) + 1) ^ (2 * n ^ 2) := by
        exact_mod_cast GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le ε i
      have hsq : Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) ≤
          ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2) := by
        have h1 : ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2 := by
          calc _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * ∫ k, ‖e i k‖ ^ 2 ∂(muK ε) := hsn
            _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * (((i : ℝ) + 1) ^ (2 * n ^ 2)) :=
                mul_le_mul_of_nonneg_left (hk.trans hd) (inv_nonneg.mpr (pow_nonneg hl.le _))
            _ = _ := by rw [mul_pow ((c * (i : ℝ) ^ α) ^ M)⁻¹, inv_pow, ← pow_mul, ← pow_mul, mul_comm M 2, mul_comm (n ^ 2) 2]
        calc _ ≤ Real.sqrt ((((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2) :=
              Real.sqrt_le_sqrt h1
          _ = _ := Real.sqrt_sq (mul_nonneg (hlnn _ (Nat.cast_nonneg _)) (by positivity))
      calc _ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C| * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_nonneg _)
        _ ≤ |C| * (1 + hs y) ^ N * (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by simp only [B]; ring

end GlobalTheory.KFourier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFourier_coefficient_rapid_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  first | exact @GlobalTheory.KFourier.kFourier_coeff_decay | exact GlobalTheory.KFourier.kFourier_coeff_decay | (intros; apply GlobalTheory.KFourier.kFourier_coeff_decay <;> assumption)
end
