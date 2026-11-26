module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.WeightedHomogeneousComponentMemElimIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoC

open MeasureTheory

def lg (t : ℝ) : ℝ := Real.log ‖(t : ℂ) + I‖

theorem tI_ne (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

theorem sq_norm_tI (t : ℝ) : ‖(t : ℂ) + I‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]; simp; ring

theorem norm_tI_eq (t : ℝ) : ‖(t : ℂ) + I‖ = Real.exp (lg t) :=
  (Real.exp_log (norm_pos_iff.2 (tI_ne t))).symm

theorem lg_nonneg (t : ℝ) : 0 ≤ lg t := by
  apply Real.log_nonneg
  have h := sq_norm_tI t
  nlinarith [norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]

theorem continuous_lg : Continuous lg := by
  unfold lg
  exact (Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')

def G (σ : ℂ) (t : ℝ) : ℂ := ((t : ℂ) + I)⁻¹ ^ 2 * Complex.exp ((lg t : ℂ) * (-2 * σ))

def G' (σ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + I)⁻¹ ^ 2 * (Complex.exp ((lg t : ℂ) * (-2 * σ)) * ((lg t : ℂ) * (-2)))

theorem cConst_eq : cConst = fun σ => ∫ t, G σ t := by
  funext σ
  unfold cConst hTrans G
  congr 1; funext t
  simp only [ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, ofReal_one, one_mul]
  unfold phi
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (norm_pos_iff.2 (tI_ne t)).ne'),
    ← Complex.ofReal_log (norm_nonneg _)]
  rfl

theorem norm_G (σ : ℂ) (t : ℝ) : ‖G σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) := by
  unfold G
  rw [norm_mul, norm_pow, norm_inv, norm_tI_eq, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_G' (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by
  have : G' σ t = G σ t * ((lg t : ℂ) * (-2)) := by unfold G G'; ring
  rw [this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]
  simp; ring

theorem bound_G {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G σ t‖ ≤ Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G]
  apply Real.exp_le_exp.2
  have := lg_nonneg t
  nlinarith

theorem bound_G' {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G']
  have hL := lg_nonneg t
  have h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t) := Real.add_one_le_exp _
  have h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg t)
    rw [show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]
    rw [div_le_iff₀ hp]
    linarith
  calc Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t)
      ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) * (2 * lg t) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = Real.exp (-(1 + ε) * lg t) * (Real.exp (-(ε * lg t)) * (2 * lg t)) := by ring
    _ ≤ Real.exp (-(1 + ε) * lg t) * (2 / ε) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / ε * Real.exp (-(1 + ε) * lg t) := by ring

theorem integrable_expL {ε : ℝ} (hε : 0 < ε) : Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg t)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 1 + ε) (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← sq_norm_tI, norm_tI_eq, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 1; push_cast; ring

theorem hasDerivAt_G (σ : ℂ) (t : ℝ) : HasDerivAt (fun s => G s t) (G' σ t) σ := by
  unfold G G'
  have h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)
  exact h.cexp.const_mul _

theorem continuous_G (σ : ℂ) : Continuous (G σ) := by
  unfold G
  have : Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹ :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne
  exact (this.pow 2).mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))

theorem continuous_G' (σ : ℂ) : Continuous (G' σ) := by
  have : G' σ = fun t => G σ t * ((lg t : ℂ) * (-2)) := by funext t; unfold G G'; ring
  rw [this]
  exact (continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)

end GlobalTheory.HeckeTwoC

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC

theorem cConst_differentiableOn : DifferentiableOn ℂ cConst halfPlane := by
  rw [cConst_eq]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    simp only [sub_re] at h3
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G')
    (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable)
    ((integrable_expL hε).mono' (continuous_G σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_G hε (hball σ₀ (Metric.mem_ball_self hε)) t))
    (continuous_G' σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_G' hε (hball σ hσ) t)
    ((integrable_expL hε).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_G σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOnStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.cConst_differentiableOn | exact GlobalTheory.HeckeTwo.cConst_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.cConst_differentiableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

theorem exists_mul_pow_mem_incidenceIdeal_of_generic {σ β K F : Type*} [Fintype σ] [CommRing K]
    [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p)
    {h : MvPolynomial (β × σ) (MvPolynomial σ K)}
    (hf : map (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom h ∈
      Ideal.span (Set.range (linForm ξ : β → _))) (j : σ) :
    ∃ m : ℕ, h * C (X j ^ m) ∈ incidenceIdeal (β := β) p := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  by_cases hj : ξ j = 0
  · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
      rw [pow_one, ← hξ, aeval_X, hj]))⟩
  obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j h
  refine ⟨m, ?_⟩
  have h1 := map_mem_span_linForm φ hg
  rw [hφ, map_sub, map_mul, map_rename] at h1
  have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
    rwa [sub_sub_cancel] at this
  rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
    linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
  have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
  rw [hker] at h2
  have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
    rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
    refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
    simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
  have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
  rwa [sub_add_cancel] at this

theorem exists_field_generic_point {σ K : Type} [CommRing K] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : σ → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ p) ∧ ξ ≠ 0 :=
  ⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p,
    aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩

theorem eq_zero_of_mem_elimIdeal_of_forall_meets {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal (β := Unit) P) : f = 0 := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro t
  obtain ⟨y, hy, hyP, hs⟩ := hP (fun j => t ((), j))
  have := aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf
  rw [map_zero, eval_map, ← aeval_def, this]

theorem exists_prime_saturation_generic_section (K L : Type) [Field K] [Field L] (N : ℕ)
    [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L]
    (P : Ideal (MvPolynomial (Fin N) K)) (hprime : P.IsPrime)
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧
      P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} ≤ Q ∧
      ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈
        P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} := by
  classical
  have hex : ∃ j, X j ∉ P := by
    obtain ⟨y, hy, hyP, -⟩ := hP 0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact ⟨j, fun h => hj (by simpa using hyP _ h)⟩
  obtain ⟨F, _, _, ξ, hξ, hne⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : Fin N → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ P) ∧ ξ ≠ 0 :=
    exists_field_generic_point hex
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  have hq := isPrime_span_linForm (ι := Unit) ξ (Ne.isUnit hj₀) Set.univ
  rw [Set.image_univ] at hq
  set q : Ideal (MvPolynomial (Unit × Fin N) F) :=
    Ideal.span (Set.range (linForm ξ : Unit → _)) with hqdef
  obtain ⟨Ω, _, π, hπ⟩ : ∃ (Ω : Type) (_ : Field Ω) (π : MvPolynomial (Unit × Fin N) F →+* Ω),
      ∀ a, π a = 0 ↔ a ∈ q := by
    refine ⟨FractionRing (MvPolynomial (Unit × Fin N) F ⧸ q), inferInstance,
      (algebraMap (MvPolynomial (Unit × Fin N) F ⧸ q) _).comp (Ideal.Quotient.mk q), fun a => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρ : MvPolynomial (Fin N) K →+* MvPolynomial (Unit × Fin N) K :=
    (rename (fun j => ((), j)) : _ →ₐ[K] _).toRingHom
  let θ : MvPolynomial (Fin N) K →+* Ω := π.comp ((map (algebraMap K F)).comp ρ)
  have hθ : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : ρ a ∈ elimIdeal (β := Unit) P :=
      (mem_elimIdeal_iff_of_generic hξ hne).2 ((hπ _).1 ha)
    have h2 := eq_zero_of_mem_elimIdeal_of_forall_meets hP h1
    apply rename_injective (fun j : Fin N => ((), j)) (fun _ _ h => (Prod.ext_iff.1 h).2)
    rw [map_zero]
    exact h2
  let θL : L →+* Ω := IsFractionRing.lift hθ
  have hθL (a) : θL (algebraMap _ L a) = θ a := IsFractionRing.lift_algebraMap hθ a
  have hθK (a : K) : θL (algebraMap K L a) = π (C (algebraMap K F a)) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L, hθL]
    simp [θ, ρ]
  let ev : MvPolynomial (Fin N) L →+* Ω := eval₂Hom θL (fun j => π (C (ξ j)))
  let Ψ : MvPolynomial (Unit × Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) L :=
    eval₂Hom (map (algebraMap K L))
      (fun v => C (algebraMap (MvPolynomial (Fin N) K) L (X v.2)))
  let φ : MvPolynomial (Fin N) K →+* F := (aeval ξ : MvPolynomial (Fin N) K →ₐ[K] F).toRingHom
  have hcomp : ev.comp Ψ = π.comp (map φ) := by
    ext a
    · simp [ev, Ψ, φ, hθK]
    · simp [ev, Ψ, φ]
    · simp [ev, Ψ, φ, hθL, θ, ρ]
  have hcomp' (h) : ev (Ψ h) = π (map φ h) := DFunLike.congr_fun hcomp h
  have hΨC (a) : Ψ (C a) = map (algebraMap K L) a := by simp [Ψ]
  have hΨL : Ψ (genericForm (K := K) (σ := Fin N) ()) =
      ∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [genericForm_eq, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [Ψ, mul_comm]
  have hΨc (c : MvPolynomial (Fin N) K) : Ψ (map C (ρ c)) = C (algebraMap _ L c) := by
    have : Ψ.comp ((map C).comp ρ) = C.comp (algebraMap _ L) := by
      ext a
      · simp [Ψ, ρ, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · simp [Ψ, ρ]
    exact DFunLike.congr_fun this c
  have hden (g : MvPolynomial (Fin N) L) : ∃ c : MvPolynomial (Fin N) K, c ≠ 0 ∧
      ∃ h, Ψ h = C (algebraMap _ L c) * g := by
    induction g using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin N) K) a
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      refine ⟨y, hy0, map C (ρ x), ?_⟩
      have : algebraMap _ L y ≠ 0 := by
        simpa using hy0
      rw [hΨc, ← C_mul, mul_div_cancel₀ _ this]
    | add f g hf hg =>
      obtain ⟨c, hc, h, hh⟩ := hf
      obtain ⟨d, hd, k, hk⟩ := hg
      refine ⟨c * d, mul_ne_zero hc hd, map C (ρ d) * h + map C (ρ c) * k, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hΨc, hΨc, hh, hk, map_mul, map_mul]
      ring
    | mul_X f v hf =>
      obtain ⟨c, hc, h, hh⟩ := hf
      refine ⟨c, hc, h * C (X v), ?_⟩
      rw [map_mul, hh, hΨC, map_X, mul_assoc]
  refine ⟨RingHom.ker ev, RingHom.ker_isPrime ev, ?_, ?_⟩
  · refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, ← hΨC, hcomp', map_C]
      have : φ g = 0 := (hξ g).2 hg
      rw [this, map_zero, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← hΨL,
        hcomp', hπ, genericForm, map_linForm]
      have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
      rw [hφ]
      exact Ideal.subset_span ⟨(), rfl⟩
  · intro g hg j
    obtain ⟨c, hc, h, hh⟩ := hden g
    have h1 : map φ h ∈ q := by
      rw [← hπ, ← hcomp', hh, map_mul, (RingHom.mem_ker.1 hg), mul_zero]
    obtain ⟨m, hm⟩ := exists_mul_pow_mem_incidenceIdeal_of_generic hξ h1 j
    refine ⟨m, ?_⟩
    have hle : incidenceIdeal (β := Unit) P ≤ Ideal.comap Ψ
        (P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)}) := by
      refine incidenceIdeal_le.2 ⟨fun a ha => ?_, fun i => ?_⟩
      · rw [Ideal.mem_comap, hΨC]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
      · rw [Ideal.mem_comap, hΨL]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h2 := hle hm
    rw [Ideal.mem_comap, map_mul, hh, hΨC, map_pow, map_X] at h2
    have hcL : algebraMap _ L c ≠ 0 := by simpa using hc
    have h3 := Ideal.mul_mem_left _ (C (algebraMap _ L c)⁻¹) h2
    convert h3 using 1
    rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, inv_mul_cancel₀ hcL, C_1, one_mul, mul_comm]

end GlobalTheory.Chow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open Filter Topology

namespace GlobalTheory.WpFam.RowReal

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma norm_add_intCast_eq_abs_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (m : ℤ) :
    ‖w + m‖ = |(m : ℝ) + w.re| := by
  have h : w + m = ((w.re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  rw [h, Complex.norm_real, Real.norm_eq_abs, add_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma exists_pos_le_norm_add_intCast_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (hn : ∀ n : ℤ, w ≠ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ ‖w + m‖ := by
  have hwx : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  have hf0 : 0 < Int.fract w.re := by
    rcases (Int.fract_nonneg w.re).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hn ⌊w.re⌋
      have h2 := Int.floor_add_fract w.re
      rw [← h, add_zero] at h2
      exact Complex.ext (by simp [h2]) (by simp [hw])
  have hf1 := Int.fract_lt_one w.re
  refine ⟨min (Int.fract w.re) (1 - Int.fract w.re), lt_min hf0 (by linarith), fun m => ?_⟩
  rw [norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hx := Int.floor_add_fract w.re
  rcases le_or_gt 0 (⌊w.re⌋ + m) with h | h
  · have h' : (0 : ℝ) ≤ ((⌊w.re⌋ + m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have h' : ((⌊w.re⌋ + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌊w.re⌋ + m ≤ -1)
    push_cast at h'
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_of_real_of_continuousAt {w : ℂ} (hw : w.im = 0)
    (hn : ∀ n : ℤ, w ≠ n) {k : ℕ} (hk : 2 ≤ k) {G : ℂ → ℂ} (hG : ContinuousAt G w)
    (hEq : ∀ z : ℂ, 0 < z.im → ∑' m : ℤ, 1 / (z + m) ^ k = G z) :
    ∑' m : ℤ, 1 / (w + m) ^ k = G w := by
  obtain ⟨δ, hδ, hδm⟩ := exists_pos_le_norm_add_intCast_of_im_eq_zero hw hn
  have hsum : Summable fun m : ℤ => 2 ^ k * (1 / ‖w + m‖ ^ k) := by
    refine Summable.mul_left _ ?_
    have h := (Real.summable_one_div_int_add_rpow w.re (k : ℝ)).2
      (by exact_mod_cast (by omega : 1 < k))
    refine h.congr fun m => ?_
    rw [Real.rpow_natCast, norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hlow : ∀ (m : ℤ) (x : ℂ), x ∈ Metric.closedBall w (δ / 2) → ‖w + m‖ / 2 ≤ ‖x + m‖ := by
    intro m x hx
    have hxw : ‖x - w‖ ≤ δ / 2 := by rw [← dist_eq_norm]; exact hx
    have h1 := hδm m
    have h2 := norm_sub_norm_le (w + m) (x + m)
    rw [show (w + (m : ℂ)) - (x + m) = -(x - w) by ring, norm_neg] at h2
    linarith
  have hcont : ContinuousOn (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k)
      (Metric.closedBall w (δ / 2)) := by
    refine continuousOn_tsum (fun m => ?_) hsum (fun m x hx => ?_)
    · refine ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun x hx => pow_ne_zero _ ?_)
      have h1 := hlow m x hx
      have h2 := hδm m
      exact norm_ne_zero_iff.mp (by linarith)
    · have hpos : 0 < ‖w + m‖ / 2 := by linarith [hδm m]
      rw [norm_div, norm_one, norm_pow]
      calc 1 / ‖x + m‖ ^ k ≤ 1 / (‖w + m‖ / 2) ^ k :=
            one_div_le_one_div_of_le (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (hlow m x hx) k)
        _ = 2 ^ k * (1 / ‖w + m‖ ^ k) := by rw [div_pow, one_div_div, mul_one_div]
  have hcw : ContinuousAt (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) w :=
    hcont.continuousAt (Metric.closedBall_mem_nhds w (by linarith))
  have hpath : Tendsto (fun ε : ℝ => w + ε * Complex.I) (𝓝[>] 0) (𝓝 w) := by
    have hc : Continuous (fun ε : ℝ => w + ε * Complex.I) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((hcw.tendsto.comp hpath).congr' ?_) (hG.tendsto.comp hpath)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEq _ (by simpa [hw] using hε)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_sq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h, tsum_coe_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_sq_mul_geometric_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hne : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linear_combination -h
    rw [this, norm_one] at hr
    exact lt_irrefl _ hr
  have hS : Summable fun n : ℕ => (n : ℂ) ^ 2 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hS1 : Summable fun n : ℕ => (n : ℂ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hG : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hr
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one hr
  have hg := tsum_geometric_of_norm_lt_one hr
  have hsplit := hS.tsum_eq_zero_add
  have hshift : (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * r ^ (n + 1))
      = fun n : ℕ => r * ((n : ℂ) ^ 2 * r ^ n) + 2 * r * ((n : ℂ) * r ^ n) + r * r ^ n := by
    funext n
    push_cast
    ring
  rw [hshift, ((hS.mul_left r).add (hS1.mul_left (2 * r))).tsum_add (hG.mul_left r),
    (hS.mul_left r).tsum_add (hS1.mul_left (2 * r)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    h1, hg] at hsplit
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add] at hsplit
  set S := ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n
  have e1 : r / (1 - r) ^ 2 * (1 - r) ^ 2 = r := div_mul_cancel₀ _ (pow_ne_zero 2 hne)
  have e2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ hne
  rw [eq_div_iff (pow_ne_zero 3 hne)]
  linear_combination (1 - r) ^ 2 * hsplit + 2 * r * e1 + r * (1 - r) * e2

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_three_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 3) := by
  have h := EisensteinSeries.qExpansion_identity (k := 2) (by norm_num) ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h
  rw [h, tsum_sq_mul_geometric_of_norm_lt_one hq]
  ring


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
theorem _root_.GlobalTheory.WpFam.RowReal.row_real : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  intro w hw hn
  have hne : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) ≠ 0 := by
    intro h
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) = 1 := by linear_combination -h
    obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.mp h1
    apply hn n
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    linear_combination hn'
  have hE : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) w := by
    fun_prop
  have hD2 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 2) w := by
    fun_prop
  have hD3 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 3) w := by
    fun_prop
  have hN3 : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)
      * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x))) w := by
    fun_prop
  constructor
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 2) hw hn le_rfl
      (continuousAt_const.mul (hE.div hD2 (pow_ne_zero 2 hne)))
      tsum_one_div_add_int_sq_of_im_pos
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 3) hw hn (by norm_num)
      (continuousAt_const.mul (hN3.div hD3 (pow_ne_zero 3 hne)))
      tsum_one_div_add_int_pow_three_of_im_pos

end GlobalTheory.WpFam.RowReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonIntegerStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  first | exact @GlobalTheory.WpFam.RowReal.row_real | exact GlobalTheory.WpFam.RowReal.row_real | (intros; apply GlobalTheory.WpFam.RowReal.row_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIff
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.LenMap

theorem isTorsionFree_submodule {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M]
    [Module R M] (h : ∀ (c : R) (x : M), c ≠ 0 → c • x = 0 → x = 0) (N : Submodule R M) :
    Module.IsTorsionFree R N := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have h1 : r • ((x : M) - y) = 0 := by
    have := congrArg Subtype.val hxy
    simp only [SetLike.val_smul] at this
    rw [smul_sub, this, sub_self]
  exact Subtype.ext (sub_eq_zero.1 (h r _ hr0 h1))

theorem exists_basis_sum {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') (Z : Submodule R M) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d : Basis ι R ↥(Z ⊓ LinearMap.ker f)) (e : Basis κ R ↥(Z.map f))
    (σ : κ → M) (hσZ : ∀ j, σ j ∈ Z) (hσf : ∀ j, f (σ j) = e j) :
    ∃ b : Basis (ι ⊕ κ) R Z, ∀ k, (b k : M) = Sum.elim (fun i => (d i : M)) σ k := by
  classical
  let w : ι ⊕ κ → M := Sum.elim (fun i => (d i : M)) σ
  have hwZ : ∀ k, w k ∈ Z := by
    rintro (i | j)
    · exact (Submodule.mem_inf.1 (d i).2).1
    · exact hσZ j
  let u : ι ⊕ κ → Z := fun k => ⟨w k, hwZ k⟩
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  have hdli : LinearIndependent R (fun i => (d i : M)) :=
    d.linearIndependent.map' (Z ⊓ LinearMap.ker f).subtype (Submodule.ker_subtype _)
  have heli : LinearIndependent R (fun j => (e j : M')) :=
    e.linearIndependent.map' (Z.map f).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent R u := by
    apply LinearIndependent.of_comp Z.subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i, g (Sum.inl i) • (d i : M) + ∑ j, g (Sum.inr j) • σ j = 0 := by
      simpa [Fintype.sum_sum_type, u, w] using hg
    have h2 : ∑ j, g (Sum.inr j) • (e j : M') = 0 := by
      have := congrArg f hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_add (f := _), map_sum, map_smul, hdf, hσf] using this
    have hr : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.1 heli _ h2
    have h1 : ∑ i, g (Sum.inl i) • (d i : M) = 0 := by simpa [hr] using hg'
    have hl : ∀ i, g (Sum.inl i) = 0 := Fintype.linearIndependent_iff.1 hdli _ h1
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range u) := by
    rintro ⟨z, hz⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hfz : f z ∈ Z.map f := Submodule.mem_map_of_mem hz
    let bb := e.repr ⟨f z, hfz⟩
    have hy : (∑ j, bb j • (e j : M')) = f z := by
      have h0 := congrArg Subtype.val (e.sum_repr ⟨f z, hfz⟩)
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul] using h0
    have hk : z - ∑ j, bb j • σ j ∈ Z ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.2 ⟨Z.sub_mem hz (Z.sum_mem fun j _ => Z.smul_mem _ (hσZ j)), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hσf]
      rw [hy, sub_self]
    have hkk := congrArg Subtype.val (d.sum_repr ⟨_, hk⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hkk
    refine ⟨Sum.elim (d.repr ⟨_, hk⟩) bb, ?_⟩
    apply Subtype.ext
    rw [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, u, w]
    rw [hkk, sub_add_cancel]
  exact ⟨Basis.mk hli hsp, fun k => by simp [u, w]⟩

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
  [Module (Int0 v) M]

theorem val_det_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b c : Basis ι (Int0 v) X) (b' c' : Basis ι (Int0 v) X')
    (A B : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M))
    (hB : ∀ k, (c' k : M) = ∑ i, B i k • (c i : M)) : v (A.det : C) = v (B.det : C) := by
  have key : ∀ (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
      (A : Matrix ι ι (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
    v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]

theorem relLen_iff_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
    (A : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) (r : ℝ) :
    RelLen v X' X r ↔ v (A.det : C) = r := by
  constructor
  · rintro ⟨n, c, c', B, hB, hr⟩
    let e := b.indexEquiv c
    rw [← hr, ← Matrix.det_reindex_self e.symm B]
    refine val_det_eq v hle b (c.reindex e.symm) b' (c'.reindex e.symm) A _ hA fun k => ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hB]
    exact (Equiv.sum_comp e (fun i => B i (e k) • (c i : M))).symm
  · intro h
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, b.reindex e, b'.reindex e, Matrix.reindex e e A, fun k => ?_, ?_⟩
    · simp only [Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [hA]
      exact (Equiv.sum_comp e.symm (fun i => A i (e.symm k) • (b i : M))).symm
    · rw [Matrix.det_reindex_self]; exact h

theorem card_eq_of_relLen {ι ι' : Type} [Fintype ι] [Fintype ι'] {X' X : Submodule (Int0 v) M}
    {r : ℝ} (h : RelLen v X' X r) (b : Basis ι (Int0 v) X) (b' : Basis ι' (Int0 v) X') :
    Fintype.card ι = Fintype.card ι' := by
  obtain ⟨n, c, c', -, -, -⟩ := h
  rw [Fintype.card_congr (b.indexEquiv c), Fintype.card_congr (b'.indexEquiv c')]

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

theorem relLen_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  intro C _ v M M' _ _ _ _ htM htM' f X' X hle hker hX hX' r
  classical
  haveI := isTorsionFree_submodule htM' (X.map f)
  haveI := isTorsionFree_submodule htM' (X'.map f)
  haveI := isTorsionFree_submodule htM (X ⊓ LinearMap.ker f)
  haveI : Module.Finite (Int0 v) (X.map f) := Module.Finite.map X f
  haveI : Module.Finite (Int0 v) (X'.map f) := Module.Finite.map X' f
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X.map f)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X'.map f)
  let g : X →ₗ[Int0 v] X.map f := f.submoduleMap X
  have hg : Function.Surjective g := f.submoduleMap_surjective X
  haveI : Module.FinitePresentation (Int0 v) (X.map f) := Module.finitePresentation_of_projective _ _
  have hfg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hg
  have hK : (LinearMap.ker g).map X.subtype = X ⊓ LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [g] using this
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [g] using hfx), rfl⟩
  haveI : Module.Finite (Int0 v) ↥(X ⊓ LinearMap.ker f) := by
    rw [Module.Finite.iff_fg, ← hK]
    exact hfg.map _
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := ↥(X ⊓ LinearMap.ker f))
  have hK' : X' ⊓ LinearMap.ker f = X ⊓ LinearMap.ker f :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf hker inf_le_right)
  obtain ⟨q, ⟨d⟩⟩ : ∃ q : ℕ, Nonempty (Basis (Fin q) (Int0 v) ↥(X ⊓ LinearMap.ker f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p, ⟨c⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p', ⟨c'⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X'.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  let d' : Basis (Fin q) (Int0 v) ↥(X' ⊓ LinearMap.ker f) := d.map (LinearEquiv.ofEq _ _ hK'.symm)
  have hd' : ∀ i, (d' i : M) = d i := fun i => rfl
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  choose σ hσX hσf using fun j => Submodule.mem_map.1 (c j).2
  choose σ' hσX' hσf' using fun j => Submodule.mem_map.1 (c' j).2
  obtain ⟨b, hb⟩ := exists_basis_sum f X d c σ hσX hσf
  obtain ⟨b', hb'⟩ := exists_basis_sum f X' d' c' σ' hσX' hσf'
  by_cases hp : p = p'
  · subst hp
    let A : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) (Int0 v) :=
      Matrix.of fun i k => b.repr (Submodule.inclusion hle (b' k)) i
    have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
      intro k
      have h0 := congrArg Subtype.val (b.sum_repr (Submodule.inclusion hle (b' k)))
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul, Submodule.coe_inclusion, A, Matrix.of_apply] using h0.symm
    rw [relLen_iff_of_basis v hle b b' A hA]
    let B := A.toBlocks₂₂
    have hB : ∀ k, (c' k : M') = ∑ j, B j k • (c j : M') := by
      intro k
      have h1 := congrArg f (hA (Sum.inr k))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hb', Sum.elim_inr, hσf', map_sum, Fintype.sum_sum_type] at h1
      simpa [hb, hdf, hσf, B, Matrix.toBlocks₂₂] using h1
    rw [relLen_iff_of_basis v (Submodule.map_mono hle) c c' B hB]
    have hinl : ∀ i, Submodule.inclusion hle (b' (Sum.inl i)) = b (Sum.inl i) := by
      intro i
      apply Subtype.ext
      rw [Submodule.coe_inclusion, hb, hb', Sum.elim_inl, Sum.elim_inl, hd']
    have h11 : A.toBlocks₁₁ = 1 := by
      ext i k
      simp [A, Matrix.toBlocks₁₁, hinl, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    have h21 : A.toBlocks₂₁ = 0 := by
      ext i k
      simp [A, Matrix.toBlocks₂₁, hinl, Finsupp.single_apply]
    have hdet : A.det = B.det := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h11, h21]
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rw [hdet]
  · constructor
    · intro h
      have := card_eq_of_relLen v h b b'
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    · intro h
      have := card_eq_of_relLen v h c c'
      simp only [Fintype.card_fin] at this
      exact absurd this hp

end GlobalTheory.LenMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIffStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLatticeRelativeLength_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  first | exact @GlobalTheory.LenMap.relLen_map_iff | exact GlobalTheory.LenMap.relLen_map_iff | (intros; apply GlobalTheory.LenMap.relLen_map_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScaling
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScaling
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_inv_signFactorial {E : Type} [AddCommGroup E] (p : ℕ) [hp : Fact p.Prime]
    (hE : ∀ x : E, p • x = 0) (a : ℕ) (ha : a < p) :
    ∃ u : ℤ, ∀ y : E, (u * ((-1 : ℤ) ^ a * (a.factorial : ℤ))) • y = y := by
  have hcop : IsCoprime ((-1 : ℤ) ^ a * (a.factorial : ℤ)) (p : ℤ) := by
    apply IsCoprime.mul_left
    · exact IsCoprime.pow_left (isCoprime_one_left.neg_left)
    · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        (fun h => absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega)))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, fun y => ?_⟩
  have h1 : u * ((-1 : ℤ) ^ a * (a.factorial : ℤ)) = 1 - v * p := by linarith
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hE, smul_zero, sub_zero]

theorem cartierAt_signFactorial : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E)
    (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) →
    (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  intro E _ p hp d γ γ' N T hE hN hγ hC
  have hp0 : 0 < p := hp.out.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [hγ 0 x hx] at h0
    simp at h0
    exact hC.inj_zero x hx h0
  · intro a x hx z hz h
    by_cases hpa : p ≤ a + 1
    · rw [hN _ hpa] at hx; exact (AddSubgroup.mem_bot.1 hx)
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      apply hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)
      rw [hγ _ x hx] at h
      rw [map_zsmul, ← h, ← mul_smul, hu]
  · intro y hy hd
    obtain ⟨x, hx, rfl⟩ := hC.surj_zero y hy hd
    exact ⟨x, hx, by rw [hγ 0 x hx]; simp⟩
  · intro a y hy hd
    obtain ⟨x, hx, z, hz, rfl⟩ := hC.surj_succ a y hy hd
    by_cases hpa : p ≤ a + 1
    · have hx0 : x = 0 := by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx
      subst hx0
      refine ⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩
      rw [hγ (a + 1) 0 (AddSubgroup.zero_mem _)]; simp
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      refine ⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩
      rw [hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScalingStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E) (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) → (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  first | exact @GlobalTheory.DI.cartierAt_signFactorial | exact GlobalTheory.DI.cartierAt_signFactorial | (intros; apply GlobalTheory.DI.cartierAt_signFactorial <;> assumption)
end
end
