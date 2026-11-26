module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

open scoped Real

noncomputable section

namespace OsgoodSeparate

theorem cons_mem_ball {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := pos_of_mem_ball hx
  refine (mem_ball_pi_iff hR).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa [Fin.tail] using (mem_ball_pi_iff hR).mp hy j

theorem cauchy_torus : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, c, _, _, _, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, G, c, R, hc, hs, r, hr0, hrR, z, hz => by
    have htor : ∀ θ, torusMap c (fun _ => r) θ ∈ ball c R := fun θ =>
      closedBall_subset_ball hrR (torusMap_mem_closedBall c hr0.le θ)
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) c (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (hc.comp_continuous (continuous_torusMap c r) htor)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    refine (torusIntegral_succ hint).trans ?_
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'R : Fin.tail z ∈ ball (Fin.tail c) R := ball_subset_ball hrR.le hz'
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr0).mp hz 0
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere (c 0) r) := by
      intro x hx
      have hxR : x ∈ ball (c 0) R := mem_ball.mpr (by rw [mem_sphere.mp hx]; exact hrR)
      have hc' : ContinuousOn (fun y => G (Fin.cons x y)) (ball (Fin.tail c) R) :=
        hc.comp (differentiable_cons_right x).continuous.continuousOn fun y hy => cons_mem_ball hxR hy
      have hs' : ∀ w ∈ ball (Fin.tail c) R, ∀ i : Fin n,
          DifferentiableAt ℂ (fun t => (fun y => G (Fin.cons x y)) (Function.update w i t)) (w i) := by
        intro w hw i
        have h := hs _ (cons_mem_ball hxR hw) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      have ih := cauchy_torus n (fun y => G (Fin.cons x y)) (Fin.tail c) R hc' hs' r hr0 hrR
        (Fin.tail z) hz'
      have e0 : c ∘ Fin.succ = Fin.tail c := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    have hcont : ContinuousOn (fun x => G (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      hc.comp (differentiable_cons_left (Fin.tail z)).continuous.continuousOn fun x hx =>
        cons_mem_ball (closedBall_subset_ball hrR hx) hz'R
    have hdiff : ∀ x ∈ ball (c 0) r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x := by
      intro x hx
      have h := hs _ (cons_mem_ball (ball_subset_ball hrR.le hx.1) hz'R) 0
      simp only [Fin.cons_zero, Fin.update_cons_zero] at h
      exact h
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end OsgoodSeparate


open OsgoodSeparate in
theorem analyticOnNhd_of_continuousOn_of_separately {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    AnalyticOnNhd ℂ g U := by
  intro c hcU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcb : ContinuousOn g (ball c ε) := hc.mono hball
  have hsb : ∀ z ∈ ball c ε, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i) :=
    fun z hz => hs z (hball hz)
  have htor : Continuous fun θ => g (torusMap c (fun _ => ε / 2) θ) :=
    hcb.comp_continuous (continuous_torusMap c _) fun θ =>
      closedBall_subset_ball hrε (torusMap_mem_closedBall c hr.le θ)
  set L := torusFunctional c (ε / 2) g htor
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern c (ε / 2) z)) c :=
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem c hr (mem_ball_self hr)))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl c (ε / 2) g (kern c (ε / 2) z) = g z
  rw [fctl_kern hr g hz, OsgoodSeparate.cauchy_torus n g c ε hcb hsb (ε / 2) hr hrε z hz, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

theorem NullSmaller.ringKrullDim_le_of_lt_succ {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'

theorem NullSmaller.proof : NullSmaller.Statement := by
  intro n d J hJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have htop : J = ⊤ := by
      by_contra h
      have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.2 h
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      exact absurd (h0.trans_lt hJ) (by simp)
    have hempty : zeroSetEuc J = ∅ := by
      ext z
      simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
    rw [hempty, measure_empty]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk := ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)
    have hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]
      refine hk.trans_lt ?_
      have : 2 * k < 2 * (k + 1) := by omega
      exact_mod_cast this
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    simpa using h0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGermValue {σ : Type} [Fintype σ] (w : σ → ℂ) : holGerms w →+* ℂ :=
  (Germ.valueRingHom (x := w)).comp (holGerms w).subtype

def holGermPointIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) : Ideal (holGerms w) :=
  RingHom.ker (holGermValue w)

def polyPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (RingHom.ker (MvPolynomial.eval w)).map (Ideal.Quotient.mk I)

def germQuotPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (holGerms w ⧸ I.map (polyGerm w)) :=
  (holGermPointIdeal w).map (Ideal.Quotient.mk _)

theorem holGermValue_polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    holGermValue w (polyGerm w q) = eval w q := rfl

theorem polyPointIdeal_isMaximal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ zeroSetIn I) : (polyPointIdeal I w).IsMaximal := by
  have hmax : (RingHom.ker (MvPolynomial.eval w)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C a⟩
  have hle : I ≤ RingHom.ker (MvPolynomial.eval w) := fun q hq => RingHom.mem_ker.2 (hw q hq)
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax).resolve_left ?_
  intro htop
  have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (RingHom.ker (MvPolynomial.eval w))
  rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle] at h
  exact hmax.ne_top h.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

namespace PrimitiveElementFibres

variable {n d : ℕ}

theorem algebraMap_C_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (a : ℂ) :
    projHom J A (C a) = Ideal.Quotient.mk J (C a) := by
  simp [projHom, pullback]
  rfl

theorem adjoin_eq_top (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    (letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤) := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro b -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a) :=
      (algebraMap_C_eq J A a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) (hx : x ∈ zeroSet J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
  Ideal.Quotient.lift J (eval x) (fun q hq => hx q hq)

theorem evalAt_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {y : Fin d → ℂ} {x : Fin n → ℂ} (hx : x ∈ fibre J A y) (P : MvPolynomial (Fin d) ℂ) :
    evalAt J x hx.1 (projHom J A P) = eval y P := by
  change eval x (pullback A P) = _
  rw [FibreBound.eval_pullback, hx.2]

theorem proof : PrimitiveElementFibres.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) := hA.injective
  obtain ⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩ :=
    PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ))
      (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)
  set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ
  have hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact algebraMap_C_eq J A (c j)

  have hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)),
      evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j) := by
    intro y x hx p
    have h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y :=
      RingHom.ext fun P => evalAt_projHom J A hx P
    have h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j := by
      rw [hℓmk]
      change eval x (∑ j, C (c j) * X j) = _
      simp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]
  refine ⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩
  ·
    have h := congrArg (Polynomial.map (eval y)) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]
    exact ⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y),
      by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · have h := congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)
      rw [hev y x hx, map_zero] at h
      exact h
    · have h := congrArg (evalAt J x hx.1) (hQ j)
      have h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) =
          eval y D := evalAt_projHom J A hx D
      have h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j := by simp [evalAt]
      rw [hev y x hx, map_mul, h3, h4] at h
      exact h
  ·
    intro τ hτ
    let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := (Polynomial.aeval ℓ).toRingHom.toAlgebra
    set_option synthInstance.maxHeartbeats 100000 in
      have : IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
        IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
    have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩
    let evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))
    have hmax : (RingHom.ker evτ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)
    have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ := by
      intro p hp
      obtain ⟨q, rfl⟩ := (hdiv p).mp hp
      rw [RingHom.mem_ker, map_mul]
      have : evτ m = 0 := hτ
      rw [this, zero_mul]
    obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker
    have hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ P.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    have hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P := by
      intro p hp
      have : p ∈ (RingHom.ker evτ) := hp
      rw [← hPc] at this
      exact this
    have hxZ : x ∈ zeroSet J :=
      fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)
    refine ⟨x, ⟨hxZ, ?_⟩, ?_⟩
    · funext i
      have h1 := hover (Polynomial.C (X i - C (y i))) (by simp [evτ])
      rw [Polynomial.aeval_C] at h1
      have h2 := hmem (pullback A (X i - C (y i))) h1
      rw [FibreBound.eval_pullback] at h2
      simpa [sub_eq_zero] using h2
    · have h1 := hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk] at h1
      have h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ) := algebraMap_C_eq J A τ
      rw [h3, ← map_sub] at h1
      have h2 := hmem _ h1
      simpa [sub_eq_zero] using h2

end PrimitiveElementFibres

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermPrimitiveForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ AnalyticAt ℂ δ (A x) ∧ (∀ i j, AnalyticAt ℂ (q i j) (A x)) ∧
      (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      (∀ᶠ z in 𝓝 x, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (∀ᶠ y in 𝓝 (A x), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      ∀ i, ∀ᶠ z in 𝓝 x, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem isRoot_map_eval_of_mem_zeroSetIn {n m : ℕ} {I : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)}
    {w : Fin n ⊕ Fin m → ℂ} (hw : w ∈ zeroSetIn I) (i : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (hP : P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ I) :
    (P.map (eval (firstCoords w))).IsRoot (w (Sum.inr i)) := by
  have h0 := hw _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval w).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom =
      eval (firstCoords w) := by
    ext q
    · simp
    · simp [firstCoords]
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem norm_lt_of_isRoot_map_eval {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by
  have hQm : (P.map (eval x)).Monic := hPm.map _
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hQm.ne_zero ha
  have hcb : Polynomial.cauchyBound (P.map (eval x)) ≤
      (∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hQm.leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
    gcongr
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map]
    exact Finset.single_le_sum (f := fun j => ‖eval x (P.coeff j)‖₊) (fun _ _ => zero_le) hj
  have h := hlt.trans_le hcb
  rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] at h
  simp only [coe_nnnorm] at h
  linarith

theorem NormalModelProper.proof : NormalModelProper.Statement := by
  intro n J M K hK
  choose P hPm hP using M.integral
  set f : (Fin n → ℂ) → ℝ := fun x =>
    ∑ i, ∑ j ∈ Finset.range (P i).natDegree, ‖eval x ((P i).coeff j)‖ with hf
  have hfc : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (MvPolynomial.continuous_eval _).norm
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  refine isBounded_iff_forall_norm_le.2 ⟨max R (1 + C), fun w hw => ?_⟩
  obtain ⟨hwZ, hwK⟩ := hw
  have hxR : ‖firstCoords w‖ ≤ R := hR _ hwK
  have hR0 : 0 ≤ max R (1 + C) := (norm_nonneg _).trans (hxR.trans (le_max_left _ _))
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun s => ?_
  rcases s with j | i
  · exact ((norm_le_pi_norm (firstCoords w) j).trans hxR).trans (le_max_left _ _)
  · have hroot := isRoot_map_eval_of_mem_zeroSetIn hwZ i (P i) (hP i)
    have hlt := norm_lt_of_isRoot_map_eval (hPm i) (firstCoords w) hroot
    have hfi : ∑ j ∈ Finset.range (P i).natDegree, ‖eval (firstCoords w) ((P i).coeff j)‖ ≤
        f (firstCoords w) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (P i).natDegree,
        ‖eval (firstCoords w) ((P i).coeff j)‖) (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have hfC : f (firstCoords w) ≤ C := by
      have := hC _ (subset_closure hwK)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    exact (hlt.le.trans (by linarith)).trans (le_max_right _ _)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetsDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionSheetsDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {y | y ∈ X ∧ ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

theorem nonempty_normalModel_of_presentation {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker

theorem NormalModelExists.proof : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def LocalGraphMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ R : ℝ, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R) ≤
      ∑ I ∈ Finset.univ.powersetCard d,
        (⨆ x : I → ℂ, frameFibreCount b I S x) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem DiscriminantCover.proof (hP : PrimitiveElementFibres.Statement) :
    DiscriminantCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨c, m, Δ, Q, hmon, hdeg, hΔ, hgood⟩ := hP n d J A hJ hdim hA
  set ℓ : (Fin n → ℂ) → ℂ := fun x => ∑ j, c j * x j with hℓ

  have hdet : ∀ w, eval w Δ ≠ 0 → ∀ x ∈ fibre J A w,
      x = fun j => ((Q j).map (eval w)).eval (ℓ x) / eval w Δ := by
    intro w hw x hx
    funext j
    rw [eq_div_iff hw, mul_comm]
    exact ((hgood w hw).2.1 x hx).2 j
  refine ⟨Δ, hΔ, fun y hy => ?_⟩
  obtain ⟨hsep, hfib, hsurj⟩ := hgood y hy
  have hm0 : m.map (eval y) ≠ 0 := (hmon.map _).ne_zero
  have hinj : Set.InjOn ℓ (fibre J A y) := fun x hx x' hx' h => by
    rw [hdet y hy x hx, hdet y hy x' hx', h]
  have himg : ℓ '' fibre J A y = ↑(m.map (eval y)).roots.toFinset := by
    ext τ
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hm0]
    exact ⟨fun ⟨x, hx, hτ⟩ => hτ ▸ (hfib x hx).1, fun h => hsurj τ h⟩
  have hfin : (fibre J A y).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact Finset.finite_toSet _) hinj
  refine ⟨hfin, ?_, fun x hx => ?_⟩
  · rw [← hinj.ncard_image, himg, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmon.natDegree_map, hdeg]

  have hroot : (m.map (eval y)).IsRoot (ℓ x) := (hfib x hx).1
  have hder : (m.map (eval y)).derivative.eval (ℓ x) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero (x := ℓ x) (by simpa [Polynomial.aeval_def] using hroot)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨U₀, B, ψ, hU₀o, hyU₀, hBo, hτB, hψd, hψy, hψ⟩ := SimpleRootBranch.proof d m y (ℓ x) hroot hder
  set U : Set (Fin d → ℂ) := U₀ ∩ {w | eval w Δ ≠ 0} with hU
  have hUo : IsOpen U := hU₀o.inter (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const)
  set g : (Fin d → ℂ) → (Fin n → ℂ) :=
    fun w j => ((Q j).map (eval w)).eval (ψ w) / eval w Δ with hg

  have hkey : ∀ w ∈ U, g w ∈ fibre J A w ∧ ℓ (g w) = ψ w := by
    intro w hw
    have hr : (m.map (eval w)).IsRoot (ψ w) := ((hψ w hw.1).2 (ψ w) (hψ w hw.1).1).mpr rfl
    obtain ⟨x', hx', hℓx'⟩ := (hgood w hw.2).2.2 (ψ w) hr
    have hℓx'' : ℓ x' = ψ w := hℓx'
    have he : x' = g w := by rw [hdet w hw.2 x' hx']; simp only [hg]; rw [hℓx'']
    exact ⟨he ▸ hx', he ▸ hℓx'⟩
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hAc : Continuous fun z : Fin n → ℂ => A.mulVec z := continuous_const.matrix_mulVec continuous_id
  refine ⟨U, {z | A.mulVec z ∈ U ∧ ℓ z ∈ B}, g, hUo, ⟨hyU₀, hy⟩,
    (hUo.preimage hAc).inter (hBo.preimage hℓc), ⟨by rw [hx.2]; exact ⟨hyU₀, hy⟩, hτB⟩,
    fun w hw => ?_, ?_, fun w hw => (hkey w hw).1.2, ?_⟩
  ·
    have hψw : DifferentiableAt ℂ ψ w := (hψd w hw.1).differentiableAt (hU₀o.mem_nhds hw.1)
    refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)
    have hΔd : DifferentiableAt ℂ (fun w => eval w Δ) w :=
      (AnalyticOnNhd.eval_mvPolynomial Δ w trivial).differentiableAt
    have hF : DifferentiableAt ℂ (fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (w, ψ w) :=
      (analyticAt_eval_map (Q j) (w, ψ w)).differentiableAt
    have hQd : DifferentiableAt ℂ (fun w => ((Q j).map (eval w)).eval (ψ w)) w :=
      DifferentiableAt.comp (g := fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2)
        (f := fun v => (v, ψ v)) w hF (differentiableAt_fun_id.prodMk hψw)
    have hfun : (fun w => g w j) = fun w => ((Q j).map (eval w)).eval (ψ w) * (eval w Δ)⁻¹ := by
      funext v; simp only [hg, div_eq_mul_inv]
    rw [hfun]
    exact hQd.mul (hΔd.inv hw.2)
  · funext j
    rw [congrFun (hdet y hy x hx) j]
    simp only [hg, hψy]
  · ext z
    constructor
    · rintro ⟨hz, hzU, hzB⟩
      have hzf : z ∈ fibre J A (A.mulVec z) := ⟨hz, rfl⟩
      have hr := ((hgood _ hzU.2).2.1 z hzf).1
      have hℓz : ℓ z = ψ (A.mulVec z) := ((hψ _ hzU.1).2 (ℓ z) hzB).mp hr
      refine ⟨A.mulVec z, hzU, ?_⟩
      funext j
      rw [congrFun (hdet _ hzU.2 z hzf) j]
      simp only [hg]
      rw [hℓz]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hf, hℓg⟩ := hkey w hw
      exact ⟨hf.1, by rw [hf.2]; exact hw, by rw [hℓg]; exact (hψ w hw.1).1⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ManifoldZerosComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Set (σ → ℂ)) (h : (σ → ℂ) → ℂ),
    IsPreconnected R → (∀ x ∈ R, IsRegularPointOf R x) → (∀ x ∈ R, AnalyticAt ℂ h x) →
    (∃ x ∈ R, h x ≠ 0) → IsPreconnected (R \ {z | h z = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def RegularLocusDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
    ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧
      ∀ B : Set (σ → ℂ), IsOpen B → B ⊆ N → X ∩ B ⊆ closure (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalOpenMapping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalOpenMapping.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
    ∃ O : Set (σ → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def holGermIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (f : Fin k → (σ → ℂ) → ℂ) : Ideal (holGerms w) :=
  Ideal.span {φ | ∃ i, (φ : Germ (𝓝 w) ℂ) = (f i : Germ (𝓝 w) ℂ)}

def PrimeGermNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → AnalyticAt ℂ g w → (holGermIdeal w p).IsPrime →
    (∀ᶠ z in 𝓝 w, (∀ i, p i z = 0) → g z = 0) →
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, g z = ∑ i, h i z * p i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def VarietySlabMeasure.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d → linForm u ∉ J → ∀ R : ℝ,
      ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphAreaHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaHolomorphic.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
      μH[((2 * d : ℕ) : ℝ)] (graphPt e F '' A) =
        ∫⁻ x in A, ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyProjectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def rowsProj {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 ((U.submatrix s id).mulVec fun j => z j)


open Classical in
def VarietyProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

def HomogDimZeroPow.Statement : Prop :=
  ∀ (n : ℕ) (K : Ideal (MvPolynomial (Fin n) ℂ)),
    K.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) ≤ 0 → ∃ N : ℕ, originIdeal n ^ N ≤ K

theorem originIdeal_eq_ker (n : ℕ) :
    originIdeal n = RingHom.ker (constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  ext f
  rw [originIdeal, ← Set.image_univ, mem_ideal_span_X_image, RingHom.mem_ker, constantCoeff_eq]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.2 h0)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact mem_support_iff.1 hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
    exact ⟨i, Set.mem_univ _, hi⟩

theorem originIdeal_isMaximal (n : ℕ) : (originIdeal n).IsMaximal := by
  rw [originIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end
