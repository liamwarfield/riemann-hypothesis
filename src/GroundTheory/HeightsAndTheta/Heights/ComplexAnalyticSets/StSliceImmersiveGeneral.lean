module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def SliceImmersiveGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    p ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
    (∃ N ∈ 𝓝 p, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) →
      ∃ V ∈ 𝓝 p, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V ⊆
        closure {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
          ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
            ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0}

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def CutOffLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
          SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
          HasCompactSupport F →
            Tendsto (fun k => chartInt J A (fun x => χ k x * F x) (vecCons G φ)) atTop
                (𝓝 (chartInt J A F (vecCons G φ))) ∧
              Tendsto (fun k => chartInt J A G (vecCons (fun x => χ k x * F x) φ)) atTop
                (𝓝 (chartInt J A G (vecCons F φ)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGeneralPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) ∧
            ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCoverCycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def PuncturedCoverCycles.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (c : Fin (e + 1) → ℂ) (r : ℝ)
    (X : Set (Fin n → ℂ)),
    0 < r → c 0 = 0 →
    (∀ x ∈ X, dist (A *ᵥ x) c < r ∧ (A *ᵥ x) 0 ≠ 0) →
    (∀ y : Fin (e + 1) → ℂ, dist y c < r → y 0 ≠ 0 → {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧
      (∀ b, DifferentiableOn ℂ (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b, ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ψ b t ∈ X ∧ A *ᵥ ψ b t = Function.update t 0 (t 0 ^ ord b)) ∧
      (∀ b, Set.InjOn (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b b', b ≠ b' → ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ∀ t' ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t ≠ ψ b' t') ∧
      (∀ x ∈ X, dist (A *ᵥ x) c < δ ^ N →
        ∃ b, ∃ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t = x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ChartChangeSheetNull.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' → IsFiniteProjection J A → IsFiniteProjection J' A' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s')}) = 0

namespace ChartChange

end ChartChange

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGramLintegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section


open scoped Classical in
open Classical in
def sheetThrough {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) : (Fin d → ℂ) → Fin n → ℂ :=
  if hs : ∃ s, IsSheetAt J A x s then hs.choose else 0

def ConeSheetGramLintegral.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A → Measurable F →
      AEMeasurable (fun y : Fin e → ℂ =>
          ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
            F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
              ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
                (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) ∧
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0} *
          ∫⁻ y : Fin e → ℂ,
            ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
              F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
                ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
                  (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem CriticalFlatNotInjective.proof : CriticalFlatNotInjective.Statement := by
  intro k U f a hk hU hf haU hJa hflat hinj
  set J : (Fin k → ℂ) → ℂ := fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hJdef
  have hJan : AnalyticOnNhd ℂ J U := fun z hz =>
    analyticAt_det_fderiv (InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hz)
  set Z : Set (Fin k → ℂ) := {z | J z = 0} with hZdef
  have hZ : IsAnalyticNear Z a := by
    refine ⟨U, 1, fun _ => J, hU, haU, fun _ => hJan, ?_⟩
    ext z
    simp only [hZdef, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
    tauto
  obtain ⟨N, hN, haN, hdense⟩ :=
    RegularLocusDense.proof AnalyticImplicitChart.proof (Fin k) Z a hZ
  have hB : IsOpen (N ∩ U) := hN.inter hU
  have ha : a ∈ closure (regLocus (Z ∩ (N ∩ U))) :=
    hdense (N ∩ U) hB Set.inter_subset_left ⟨hJa, haN, haU⟩
  obtain ⟨c, hc⟩ : (regLocus (Z ∩ (N ∩ U))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at ha
    exact ha
  obtain ⟨⟨hcZ, hcB⟩, d, A, O, V, g, hO, hV, hcV, hg, hAg, hYV⟩ := hc
  obtain ⟨y0, hy0O, hgy0⟩ : c ∈ g '' O := hYV ▸ ⟨⟨hcZ, hcB⟩, hcV⟩

  have hgO : ∀ y ∈ O, J (g y) = 0 ∧ g y ∈ U := by
    intro y hy
    have h1 : g y ∈ Z ∩ (N ∩ U) ∩ V := hYV ▸ Set.mem_image_of_mem g hy
    exact ⟨h1.1.1, h1.1.2.2⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·
    obtain ⟨z, ⟨hzV, hzB⟩, hzc, hz0⟩ := exists_zero_ne_near hk (hJan c hcB.2) hcZ
      (Filter.inter_mem (hV.mem_nhds hcV) (hB.mem_nhds hcB))
    obtain ⟨y1, -, hgy1⟩ : z ∈ g '' O := hYV ▸ ⟨⟨hz0, hzB⟩, hzV⟩
    exact hzc (by rw [← hgy1, ← hgy0, Subsingleton.elim y1 y0])
  ·
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y0 hy0O
    have hconst : ∀ y ∈ ball y0 ε, f (g y) = f (g y0) := by
      intro y hy
      have hdiff : ∀ x ∈ ball y0 ε, DifferentiableAt ℂ (f ∘ g) x := fun x hx =>
        (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)).comp x
          (hg x (hball hx)).differentiableAt
      refine (convex_ball y0 ε).is_const_of_fderivWithin_eq_zero (f := f ∘ g)
        (fun x hx => (hdiff x hx).differentiableWithinAt) (fun x hx => ?_) hy (mem_ball_self hε)
      rw [fderivWithin_of_isOpen isOpen_ball hx,
        fderiv_comp x (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2))
          (hg x (hball hx)).differentiableAt,
        hflat (g x) (hgO x (hball hx)).2 (hgO x (hball hx)).1, ContinuousLinearMap.zero_comp]
    set y1 : Fin d → ℂ := y0 + ((ε / 2 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) with hy1
    have hy1ball : y1 ∈ ball y0 ε := by
      rw [mem_ball, dist_eq_norm, hy1, add_sub_cancel_left, norm_smul, pi_norm_const, norm_one, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hy10 : y1 ≠ y0 := by
      intro h
      have h2 := congrFun (congrArg (· - y0) h) ⟨0, hd⟩
      simp only [hy1, add_sub_cancel_left, sub_self, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Complex.ofReal_eq_zero] at h2
      linarith
    have heq : g y1 = g y0 :=
      hinj (hgO y1 (hball hy1ball)).2 (hgO y0 hy0O).2 (hconst y1 hy1ball)
    exact hy10 (by rw [← hAg y1 (hball hy1ball), ← hAg y0 hy0O, heq])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametricCircleIntegralAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Metric Filter Topology Set Complex MeasureTheory

open scoped Real

noncomputable section

namespace ParametricCircleIntegralAnalytic

theorem analyticOnNhd_of_differentiableOn_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hO' : IsOpen (e.symm ⁻¹' O) := hO.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O) :=
    hf.comp e.symm.differentiableOn (fun y hy => hy)
  have ha := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg
  intro x hx
  have h1 : AnalyticAt ℂ (f ∘ e.symm) (e x) := ha (e x) (by simpa using hx)
  have h2 := h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)
  simpa [Function.comp_def] using h2

end ParametricCircleIntegralAnalytic


open ParametricCircleIntegralAnalytic in
theorem ParametricCircleIntegralAnalytic.proof : ParametricCircleIntegralAnalytic.Statement := by
  intro ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀
  have hcd : ContinuousOn (fderiv ℂ Φ) O :=
    ((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  obtain ⟨u, v, hu, -, hx₀u, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO
    (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))
  have hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O := fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hcd.mono hK)
  have hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O := fun x hx θ =>
    hK ⟨hx, circleMap_mem_sphere c hr θ⟩
  have hcont : ∀ x ∈ closedBall x₀ ε,
      Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ) := fun x hx =>
    (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
      (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε) := by
    intro x₁ hx₁
    have hs : ball x₀ ε ∈ 𝓝 x₁ := isOpen_ball.mem_nhds hx₁
    have hx₁c : x₁ ∈ closedBall x₀ ε := ball_subset_closedBall hx₁
    simp only [circleIntegral, deriv_circleMap]
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
      (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ))
      (F' := fun x θ => (circleMap 0 r θ * I) •
        (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
      (bound := fun _ => |r| * (M * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)) hs ?_ ?_ ?_ ?_ ?_
      ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [hs] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₁ hx₁c).intervalIntegrable _ _
    · refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
        ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip
          (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp
          (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ) :=
        (hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt
      exact (h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)
  exact analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHessCCompPluri
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

def HessCCompPluri.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (L : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ),
    ContDiffAt ℝ 2 F (L z) → ContDiffAt ℝ 2 L z → hessC L z = 0 →
      hessC (fun w => F (L w)) z = ((deriv (deriv F) (L z) : ℝ) : ℂ) • hessC (fun w => L w ^ 2 / 2) z

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def IsolatedFibreOpen.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (x : Fin n → ℂ),
    IsAffVariety J k → x ∈ zeroLocus J →
    (∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ zeroLocus J → A *ᵥ z = A *ᵥ x → z = x) →
    ∀ W' ∈ 𝓝 x, (fun z => A *ᵥ z) '' (zeroLocus J ∩ W') ∈ 𝓝 (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetOnlyNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

def SheetOnlyNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'}) = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffDominated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def CutOffDominated.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (χ : ℕ → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A → P ≠ 0 →
    (∀ k, Measurable (χ k)) → (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    Integrable (chartAbsDens J A f ψ) →
      Tendsto (fun k => chartInt J A (fun x => χ k x * f x) ψ) atTop (𝓝 (chartInt J A f ψ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def StokesOffDiscriminant.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s) →
    ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport F →
      (∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
        ∀ x ∈ U ∩ zeroSet J, F x = 0) →
        chartInt J A F (vecCons G φ) = chartInt J A G (vecCons F φ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def CutOffBoundaryBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    HasCompactSupport F →
      ∃ R C : ℝ, ∀ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ →
        |chartInt J A G (vecCons (fun x => χ x * F x) φ) -
            chartInt J A (fun x => χ x * G x) (vecCons F φ)| ≤
          C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y) +
            Real.sqrt (energyInt J A (Metric.closedBall 0 R) χ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedPointsNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedPointsNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∀ U ∈ 𝓝 w, ∃ z ∈ X ∩ U, δ (A z) ≠ 0 ∧
          (∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedLocusCutOut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormSheetedLocusCutOut.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ c e : (σ → ℂ) → ℂ, AnalyticAt ℂ c w ∧ AnalyticAt ℂ e w ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → c z * e z = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 →
          ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) ↔ c z = 0) ∧
          ((∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧
            z ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) → e z ≠ 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSetFrame
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

namespace SheetImageAreaSet

theorem exists_adapted_frame {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by
  classical
  set K := LinearMap.ker P with hKdef
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at h2
  simp only [finrank_euclideanSpace_fin] at h1 h2
  rw [← hKdef] at h2
  have hW : finrank ℂ Kᗮ = d := by omega
  have hn : n = d + finrank ℂ K := by omega
  let bW : OrthonormalBasis (Fin d) ℂ Kᗮ := (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hW)
  let bK := stdOrthonormalBasis ℂ K
  let e : Fin n ≃ Fin d ⊕ Fin (finrank ℂ K) := (finCongr hn).trans finSumFinEquiv.symm
  let πW : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    bW.repr.toLinearMap ∘ₗ (Kᗮ.orthogonalProjectionOnto : _ →L[ℂ] Kᗮ).toLinearMap
  let π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ K)) :=
    bK.repr.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : _ →L[ℂ] K).toLinearMap
  obtain ⟨R, hR⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ y, P (R y) = y := fun y => LinearMap.congr_fun hR y
  have hWR : ∀ z, πW (R (P z)) = πW z := by
    intro z
    have hmem : R (P z) - z ∈ Kᗮᗮ :=
      K.le_orthogonal_orthogonal (by simp [hKdef, LinearMap.mem_ker, hPR])
    have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hmem
    have h3 : πW (R (P z) - z) = 0 := by simp [πW, h0]
    rwa [map_sub, sub_eq_zero] at h3
  have hinj : Function.Injective (πW ∘ₗ R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : Kᗮ.orthogonalProjectionOnto (R y) = 0 := by simpa [πW] using hy
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, K.orthogonal_orthogonal] at h0
    rw [← hPR y]
    exact h0
  let L := LinearEquiv.ofInjectiveEndo _ hinj
  let Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j))
      map_add' := fun z w => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp
      map_smul' := fun c z => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp }
  refine ⟨finrank ℂ K, e, Q, L, π, fun z => ?_, fun z => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    show ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) :
      EuclideanSpace ℂ (Fin n))‖ ^ 2 = _
    rw [GraphAreaHolomorphic.norm_sq_sumElim e (πW z) (π z), Submodule.norm_sq_eq_add_norm_sq_projection z K,
      add_comm]
    simp [πW, π]
  · show WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) = _
    simp [L, hWR]

theorem areaJacobian_eq_normDet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by
  have h := M.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [areaJacobian, ← h, Real.sqrt_sq M.normDet_nonneg]

theorem areaJacobian_comp_of_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem areaJacobian_comp_endo {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]

end SheetImageAreaSet

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicKernelFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem HolomorphicKernelFibre.proof : HolomorphicKernelFibre.Statement := by
  intro k U f b hU hf hb d hd
  set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA
  have hfa : AnalyticAt ℂ f b := InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb
  have hfd : HasFDerivAt f A b := (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt
  set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW
  set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  have hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
    have h2 := Submodule.finrank_add_eq_of_isCompl hWC
    rw [Module.finrank_fin_fun]
    rw [← hW, ← hK, hd] at h1
    omega
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) := by
    rw [Module.finrank_fin_fun]; exact hd
  let eC : C ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimC
  let eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimK
  let P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := LinearMap.toContinuousLinearMap (W.projection C hWC)
  let E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ :=
    LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))
  let lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')
  let ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)
  have hEC : ∀ t, E t ∈ C := fun t => (eC.symm t).2
  have hEinj : Function.Injective E := fun s t hst => by
    have : eC.symm s = eC.symm t := Subtype.ext hst
    exact eC.symm.injective this
  have hPE : ∀ t, P (E t) = 0 := fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)
  have hPA : ∀ v, P (A v) = A v := fun v =>
    Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)
  have hℓA : ∀ v, ℓ (A v) = 0 := fun v => by
    have h0 : C.projectionOnto W hWC.symm (A v) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)
    show eC (C.projectionOnto W hWC.symm (A v)) = 0
    rw [h0, map_zero]

  let M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ := (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)
  have hMinj : Function.Injective M := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : A v + E (lam v) = 0 := hv
    have hAv : A v = 0 := by
      refine (Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact C.neg_mem (hEC _)
    have hlv : lam v = 0 := by
      rw [hAv, zero_add] at hv'
      exact hEinj (hv'.trans (map_zero E).symm)
    have hvK : v ∈ K := hAv
    have : eK (K.projectionOnto K' hKK' v) = 0 := hlv
    rw [Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff] at this
    exact congrArg Subtype.val this
  let M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ := (LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv
  let Φ : (Fin k → ℂ) → Fin k → ℂ := fun z => P (f z) + E (lam z)
  have hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b := by
    have h := (P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt
    have hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) := by
      ext1 v
      show P (A v) + E (lam v) = A v + E (lam v)
      rw [hPA]
    rw [hM] at h
    exact h
  have hΦc : ContDiffAt ℂ 1 Φ b :=
    (P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hHΦ : ∀ z, H z = Φ z := fun z => rfl
  have hbS : b ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hΦbT : Φ b ∈ H.target := hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
  have hHb : H.symm (Φ b) = b := by rw [← hHΦ]; exact H.left_inv hbS
  obtain ⟨O, hO, hOo, hbO⟩ := eventually_nhds_iff.mp (hinv.eventually (by simp))
  set c := P (f b) with hc
  let T := (H.target ∩ H.symm ⁻¹' U) ∩ O
  have hTo : IsOpen T := (H.isOpen_inter_preimage_symm hU).inter hOo
  let aff : (Fin d → ℂ) → Fin k → ℂ := fun t => c + E t
  have haff : Continuous aff := continuous_const.add E.continuous
  refine ⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c + E (lam b) ∈ T
    refine ⟨⟨hΦbT, ?_⟩, hbO⟩
    show H.symm (Φ b) ∈ U
    rw [hHb]; exact hb
  · intro t ht
    exact ((hO _ ht.2).differentiableAt one_ne_zero).comp t
      ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt
  · intro t ht
    exact ht.1.2
  · intro s hs t ht hst
    have h1 := H.right_inv hs.1.1
    have h2 := H.right_inv ht.1.1
    have : aff s = aff t := by rw [← h1, ← h2]; exact congrArg H hst
    exact hEinj (add_left_cancel this)
  ·
    have hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c := by
      intro t ht
      have h1 : Φ (H.symm (aff t)) = c + E t := H.right_inv ht.1.1
      have h2 := congrArg P h1
      simp only [Φ, map_add (f := _), hPE, add_zero, hPP] at h2
      rw [h2, hc, hPP]
    intro s hs t ht hst
    have hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) =
        C.projectionOnto W hWC.symm (f (H.symm (aff t))) := eC.injective hst
    rw [← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))),
      ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]
    have hs' := hfib s hs
    have ht' := hfib t ht
    simp only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'
    rw [hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]
  ·
    have hγy : H.symm (aff (lam b)) = b := hHb
    have hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b) :=
      (hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)
    have hfd' : HasFDerivAt f A (H.symm (aff (lam b))) := by rw [hγy]; exact hfd
    have h := ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)
    refine h.fderiv.trans ?_
    ext1 v
    exact hℓA _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitivePresentationCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimitivePresentationCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → IsPrimitivePresentation w p A ℓ c δ →
    ∀ W ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
      ∃ x : Fin N → σ → ℂ, (∀ j, x j ∈ W ∧ (∀ i, p i (x j) = 0) ∧ A (x j) = y) ∧
        Function.Injective fun j => ℓ (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
