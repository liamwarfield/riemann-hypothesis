module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFixedBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J →
      ∃ M : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ M

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitGoodPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitGoodPoints.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
            Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
              (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
                  (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
                (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGoodPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    q ∈ zeroSet J → linEval u q = 0 → DivisorRegularAt J u d q → NormalDivisorChartAt M u d q →
    NormalDoublePointsOnDivisor M u q →
      ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
          (π : Matrix (Fin d) (Fin n) ℂ),
          (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
          (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
          (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
          (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
          ∀ b, Function.Bijective
            (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongMassNearSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → J ⊔ Ideal.span {linForm u} ≤ I →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ δ > 0, ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ) ∧
        |∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamPieceInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamPieceInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (P : Set (Fin d → ℂ)),
      (∀ i, SmoothNear (zeroSet W) (φ i)) → MeasurableSet P → P ⊆ Metric.ball 0 r →
      (∀ w ∈ P, σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) →
      Set.InjOn (fun v => A *ᵥ σ v) P →
        chartInt W A ((σ '' P).indicator f) φ =
          ∫ w in P, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreSumInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

theorem abs_det_fderiv_real_mul_eq_normSq {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by
  intro t ht
  simp only
  rw [det_fderiv_real_eq_normSq τ t (hτ.differentiableAt (hΩ.mem_nhds ht)),
    abs_of_nonneg (Complex.normSq_nonneg _)]

theorem HolomorphicFibreSumInt.proof (h : WeightedAreaFormula.Statement) :
    HolomorphicFibreSumInt.Statement := by
  intro d Ω τ H hΩ hτ hfin hint
  have heq := abs_det_fderiv_real_mul_eq_normSq hΩ hτ H
  have hint' : IntegrableOn (fun t => |(fderiv ℝ τ t).det| * H t) Ω :=
    (integrableOn_congr_fun heq hΩ.measurableSet).2 hint
  obtain ⟨h1, h2⟩ := h (Fin d → ℂ) volume Ω τ H hΩ (hτ.restrictScalars ℝ) hfin hint'
  exact ⟨h1, h2.trans (setIntegral_congr_fun hΩ.measurableSet heq)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormWindow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormWindow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ Convex ℝ B ∧ A w ∈ B ∧
        IsOpen N' ∧ closure W ⊆ N' ∧ (∀ i, AnalyticOnNhd ℂ (f i) N') ∧
        X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} ∧
        (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) ∧
        (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ i, ∀ z ∈ X ∩ W, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) ∧
        (∀ j, AnalyticOnNhd ℂ (a j) B) ∧ AnalyticOnNhd ℂ δ B ∧ (∀ i j, AnalyticOnNhd ℂ (q i j) B) ∧
        (∀ y ∈ B, δ y ≠ 0 →
          (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorChartGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def NormalDivisorChartAtPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
    DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
    (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
    VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
    ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalModelDivisorChartGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ),
        M.ideal ⊔ Ideal.span {rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)} ≤ B ∧
        ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) < (d : ℕ) ∧
        ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0 →
          w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn B → NormalDivisorChartAtPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBundleRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def universalSliceIdeal {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :=
  J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ)) ⊔
    Ideal.span (Set.range fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j))))

theorem fibreIdeal_universalSliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (L : Matrix (Fin d) (Fin n) ℂ) :
    fibreIdeal (universalSliceIdeal J d q) (fun ij => L ij.1 ij.2) = sliceIdeal J L q := by
  rw [fibreIdeal, universalSliceIdeal, Ideal.map_sup, ← fibreIdeal, fibreIdeal_map_C, Ideal.map_span,
    sliceIdeal, ← Set.range_comp]
  have h : (MvPolynomial.map (eval fun ij : Fin d × Fin n => L ij.1 ij.2)) ∘
      (fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j)))) =
      fun i => ComplexSets.linPoly L i - C ((L *ᵥ q) i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, map_sum]
  rw [h]

def SliceBundleRadicalAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical → ∀ k : Fin n,
    IsRadicalAway (universalSliceIdeal J d q) (X k - C (C (q k)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem CutOffLimit.proof (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by
  intro n d J A P hJ hdim hA hP
  obtain ⟨χ, hχs, hχI, hχU, hχ1, hχE, hχM⟩ := hC n d J A P hJ hdim hA hP
  refine ⟨χ, hχs, hχU, fun F G φ hF hG hφ hc => ?_⟩
  have hcont : ∀ f, SmoothNear (zeroSet J) f → ContinuousOn f (zeroSet J) := by
    rintro f ⟨U, -, hU, hf⟩
    exact hf.continuousOn.mono hU
  have hcons : ∀ f, SmoothNear (zeroSet J) f → ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro f hf i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hφ i
  have hmeas : ∀ k, Measurable (χ k) := fun k => (hχs k).continuous.measurable
  refine ⟨hD n (d + 1) J A P χ F (vecCons G φ) hJ hdim hA hP hmeas hχI hχ1 (hcont F hF) (hcons G hG)
    (hM n (d + 1) J A F (vecCons G φ) hJ hdim hA (hcont F hF) (hcons G hG) (Or.inl hc)), ?_⟩
  have h1 := hD n (d + 1) J A P χ G (vecCons F φ) hJ hdim hA hP hmeas hχI hχ1 (hcont G hG) (hcons F hF)
    (hM n (d + 1) J A G (vecCons F φ) hJ hdim hA (hcont G hG) (hcons F hF) (Or.inr ⟨0, by simpa using hc⟩))
  obtain ⟨R, C, hRC⟩ := hB n d J A F G φ hJ hdim hA hF hG hφ hc
  have h0 : Tendsto (fun k => C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (χ k) φ) y) + Real.sqrt (energyInt J A (Metric.closedBall 0 R) (χ k)))) atTop (𝓝 0) := by
    simpa using ((hχM R φ hφ).add (hχE R).sqrt).const_mul C
  refine h1.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
  rw [Real.dist_eq, abs_sub_comm]
  exact hRC (χ k) (hχs k)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSliceSheetParam
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeSliceSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → Fin n → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) (s k j)) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          ({z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnVariety
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetBallCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem volume_ball_pi_complex {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by
  rw [ball_pi c hρ, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le,
    mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

theorem exists_cover_le_volume_thickening {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by
  set δ : NNReal := ⟨r / 4, by positivity⟩
  have hδ : (δ : ℝ) = r / 4 := rfl
  have hpack : packingNumber (2 * δ) A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)
  set S := maximalSeparatedSet (2 * δ) A
  have hSfin : S.Finite := Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  refine ⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩
  · refine ((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_
    refine Set.iUnion₂_subset fun c hc => ?_
    refine (closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]; linarith
    · simpa using hc
  · have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)
    have hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa using hx) (by simpa using hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1
      linarith
    have hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A := by
      refine Set.iUnion₂_subset fun c hc => ?_
      exact (ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans
        (thickening_mono (by linarith) A)
    have hvol := measure_mono (μ := volume) hsub
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const,
      nsmul_eq_mul] at hvol
    have hfin : volume (thickening r A) ≠ ⊤ := (hA.isBounded.thickening).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

theorem SmallSetBallCover.proof (h : SmallSetTubeVolume.Statement) : SmallSetBallCover.Statement := by
  intro n d I K hdim hK
  obtain ⟨C, hC0, hC⟩ := h n d I K hdim hK
  refine ⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩
  have hr0 := hr.1
  have hZ : IsClosed (zeroSet I) := by
    have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hA : IsCompact (zeroSet I ∩ K) := hK.inter_left hZ
  obtain ⟨T, hTA, hcov, hcount⟩ := exists_cover_le_volume_thickening hA hr0
  refine ⟨T, hTA, hcov, ?_⟩
  have hV := ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)
  have hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n) := by positivity
  have he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]
  have hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; ring_nf
  refine le_of_mul_le_mul_right ?_ hP
  calc (T.card : ℝ) * r ^ (2 * d) * ((Real.pi / 16) ^ n * r ^ (2 * n))
      = ((T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n) * r ^ (2 * d) := by rw [hball]; ring
    _ ≤ (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) * r ^ (2 * d) := mul_le_mul_of_nonneg_right (hcount.trans hV) (by positivity)
    _ = C * (16 / Real.pi) ^ n * r ^ 2 * ((Real.pi / 16) ^ n * r ^ (2 * n)) := by
      rw [mul_assoc, hz]
      linear_combination (-(C * r ^ (2 * n) * r ^ 2)) * he

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermGeneralCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_lastCoord_ne_zero_of_mem_nhds {σ : Type} {U : Set (Option σ → ℂ)} {w : Option σ → ℂ}
    (hU : U ∈ 𝓝 w) : ∃ v ∈ U, v none ≠ 0 := by
  classical
  let g : ℂ → Option σ → ℂ := fun s => Function.update w none s
  have hg : Continuous g := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => simpa [g] using continuous_id'
    | some i => simpa [g] using continuous_const
  have hgw : g (w none) = w := Function.update_eq_self none w
  have hev : ∀ᶠ s in 𝓝 (w none), g s ∈ U := by
    have := hg.tendsto (w none)
    rw [hgw] at this
    exact this hU
  have hne : ∀ᶠ s in 𝓝[≠] (w none), s ≠ 0 := by
    by_cases h0 : w none = 0
    · rw [h0]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨s, hs1, hs2⟩ := (((hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ s in 𝓝[≠] (w none), g s ∈ U).and hne).exists
  exact ⟨g s, hs1, by simpa [g] using hs2⟩

theorem GeneralLinearCoordinates.proof : GeneralLinearCoordinates.Statement := by
  classical
  intro σ _ f hf hnz
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd

  obtain ⟨w, hwb, hfw⟩ : ∃ w ∈ Metric.ball (0 : Option σ → ℂ) r, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun x hx => h x hx)
  have hUopen : IsOpen (Metric.ball (0 : Option σ → ℂ) r ∩ f ⁻¹' {z | z ≠ 0}) :=
    hfr.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  obtain ⟨v, ⟨hvb, hfv⟩, hvt⟩ := exists_lastCoord_ne_zero_of_mem_nhds (hUopen.mem_nhds ⟨hwb, hfw⟩)
  replace hfv : f v ≠ 0 := hfv

  let e : Option σ → ℂ := Pi.single none 1
  let L : (Option σ → ℂ) →ₗ[ℂ] (Option σ → ℂ) :=
    LinearMap.id + (LinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).smulRight (v - e)
  have hL : ∀ x, L x = x + x none • (v - e) := fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L x) none = 0 := by rw [hx]; rfl
    have hnone : x none = 0 := by
      rw [hL] at h1
      simp [e] at h1
      have h2 : x none * v none = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hvt
    rw [hL, hnone, zero_smul, add_zero] at hx
    exact hx
  let A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L hLinj).toContinuousLinearEquiv
  have hA : ∀ t : ℂ, A (pointWithLast 0 t) = t • v := by
    intro t
    show L (pointWithLast 0 t) = t • v
    rw [hL]
    funext o
    cases o with
    | none => simp [pointWithLast, e]; ring
    | some i => simp [pointWithLast, e]
  refine ⟨A, ?_⟩
  have hfun : (fun t => f (A (pointWithLast 0 t))) = fun t : ℂ => f (t • v) := by
    funext t; rw [hA]
  rw [hfun]

  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr fun h => hvt (by rw [h]; rfl)
  have hvr : ‖v‖ < r := by simpa using hvb
  set R := r / ‖v‖
  have hR1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact (one_lt_div hv0).mpr hvr
  have hR0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (lt_trans one_pos
    ((one_lt_div hv0).mpr hvr))
  have han : AnalyticOnNhd ℂ (fun t : ℂ => f (t • v)) (Metric.ball (0 : ℂ) R) := by
    intro t ht
    have htv : t • v ∈ Metric.ball (0 : Option σ → ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Metric.mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
        _ = r := div_mul_cancel₀ r hv0.ne'
    have hs : AnalyticAt ℂ (fun s : ℂ => s • v) t := analyticAt_id.smul analyticAt_const
    show AnalyticAt ℂ (f ∘ fun s : ℂ => s • v) t
    exact AnalyticAt.comp (f := fun s : ℂ => s • v) (x := t) (hfr _ htv) hs
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), f (t • v) = 0) := by
    intro h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hR0 h hR1
    simp at this
    exact hfv this
  have hne : analyticOrderAt (fun t : ℂ => f (t • v)) 0 ≠ ⊤ := fun h =>
    hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Filter ComplexSets

open scoped ENNReal

noncomputable section

namespace LogIntegrableProof

variable {n : ℕ}

theorem lintegral_lt_top (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := hS n d J u R hJ hdim hu
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hsub : S ⊆ zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ :=
    (measure_mono hsub).trans_lt (hF n d J hJ hdim (R + 1))
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => ∑ j, u j * z j := by fun_prop
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖∑ j, u j * z j‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  set M : ℝ := max (∑ j, ‖u j‖ * R) 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((norm_sum_le _ _).trans ?_)
    refine le_trans ?_ (le_max_left _ _)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le z j).trans hz.2) (norm_nonneg _)

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖∑ j, u j * z j‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (∑ j, u j * z j)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right (∑ j, ‖u j‖ * R) 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

end LogIntegrableProof


open LogIntegrableProof in
theorem LogIntegrable.proof (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianPrimeDerivations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem JacobianPrimeDerivations.proof (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermCanonicalCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermCanonicalCover.proof (h₁ : PrimeGermPrimitivePresentation.Statement)
    (h₂ : PrimitivePresentationCover.Statement) : PrimeGermCanonicalCover.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, ℓ, N, c, δ, hpres, hδ⟩ := h₁ σ w k p hp hP
  have hδa : AnalyticAt ℂ δ (A w) := hpres.2.1
  have hdiv := hpres.2.2.2.2.2.1
  refine ⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩
  intro g hg
  obtain ⟨M, a, ha, h, hh, hev⟩ := hdiv g hg
  exact ⟨M, a, h, ha, hh, hev⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedOffDiscriminant.proof (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
