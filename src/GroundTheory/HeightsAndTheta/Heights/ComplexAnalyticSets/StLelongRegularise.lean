module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def logReg (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) : ℝ :=
  Real.log (‖linEval u x‖ ^ 2 + ε) / 2

theorem contDiff_linEval (u : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Fin n → ℂ => linEval u x) := by
  unfold linEval
  exact ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) j).restrict_scalars ℝ)

theorem contDiff_logReg (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logReg u ε) := by
  unfold logReg
  refine ContDiff.div_const (ContDiff.log (((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).add
    contDiff_const) fun x => ?_) _
  have : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
  simp only [Function.comp_apply]
  linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def ChartMassCompact.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    (HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) →
      Integrable (chartAbsDens J A f ψ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def cutStep (t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t)

def cutLevel (k : ℕ) : ℝ := Real.exp (-Real.exp ((k : ℝ) + 1))

def logAbsSq {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  Real.log (‖eval y Q‖ ^ 2)

def logLogCut {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) : ℝ :=
  if ‖eval y Q‖ ^ 2 = 0 then 0
  else if 1 ≤ ‖eval y Q‖ ^ 2 then 1
  else cutStep (Real.log (-logAbsSq Q y) / ((k : ℝ) + 1))

def logLogCutAlong {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ)
    (x : Fin n → ℂ) : ℝ :=
  logLogCut Q k (A *ᵥ x)

def tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  if logAbsSq Q y ≤ -1 then (logAbsSq Q y ^ 2)⁻¹ else 0

def tubeDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Fin (d + 1) → ℂ) → ℝ :=
  chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => tubeWeight P (A *ᵥ x))
    (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ)

def CutOffShape.Statement : Prop :=
  ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ),
    (∀ k, ContDiff ℝ ∞ (logLogCut Q k) ∧ (∀ y, logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ y, ‖eval y Q‖ ^ 2 < cutLevel k → logLogCut Q k y = 0) ∧
    ∀ y, eval y Q ≠ 0 → Tendsto (fun k => logLogCut Q k y) atTop (𝓝 1)

theorem cutLevel_mem (k : ℕ) : 0 < cutLevel k ∧ cutLevel k < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def BranchProperAtPoint.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∀ s ∈ Metric.ball 0 (γ b).radius, (γ b).toFun s = x →
      ∀ P ∈ 𝓝 s, ∃ ε > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius,
        (γ b).toFun τ ∈ Metric.ball x ε → τ ∈ P

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

variable {n d : ℕ}

def chartPosDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => max (f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y

def PosPartIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f → (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) = ∫⁻ y, ENNReal.ofReal (chartPosDens J A' f φ y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
      (∀ i, SmoothNear (zeroSet W) (φ i)) →
        chartInt W A f φ =
          ∫ w in Metric.ball (0 : Fin d → ℂ) r, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

variable {n : ℕ}

def DivisorRegularAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
    (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O

def NormalDivisorChartAt {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
    ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
      DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
      Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
      (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
      VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
      ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
        fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalDoublePointsOnDivisor {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (q : Fin n → ℂ) : Prop :=
  ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i))

def IsRadicalAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  ∀ f ∈ I.radical, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * f ∈ I

theorem eval_linPoly (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem zeroSet_sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by
  ext x
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), funext fun i => ?_⟩
    have := h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rwa [map_sub, eval_linPoly, eval_C, sub_eq_zero] at this
  · rintro ⟨hJ, hL⟩ f hf
    have hle : sliceIdeal J L q ≤ RingHom.ker (eval x) := by
      refine sup_le (fun g hg => RingHom.mem_ker.2 (hJ g hg)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_linPoly, eval_C, hL, sub_self]
    exact RingHom.mem_ker.1 (hle hf)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def VanishNearPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    J.IsPrime → x ∈ zeroLocus J → (∀ᶠ y in 𝓝 x, y ∈ zeroLocus J → eval y f = 0) → f ∈ J

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def FiniteMapOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    J.IsPrime → Function.Injective ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)) →
    ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite →
    ∀ x ∈ zeroLocus J, ∀ U ∈ 𝓝 x,
      (fun z : Fin n → ℂ => fun i => eval z (p i)) '' (zeroLocus J ∩ U) ∈
        𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : ℝ :=
  areaJacobian ((WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap)

theorem sheetJac_nonneg (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : 0 ≤ sheetJac s y :=
  Real.sqrt_nonneg _

def SheetComass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ), (∀ k, SmoothNear (zeroSet J) (φ k)) →
    ∃ C : ℝ, ∀ x ∈ zeroSet J ∩ Metric.closedBall 0 R, ∀ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt J A x s →
      |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)| ≤ C * sheetJac s (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensLeibniz.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (f g : (Fin (D + 1) → ℂ) → ℝ) (z : Fin (D + 1) → ℂ),
    ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (fun y => f y * g y) φ) z =
          f z * maDens (Fin.cons g φ) z + g z * maDens (Fin.cons f φ) z + gradDens φ f g z +
            gradDens φ g f z ∧
        maDens (Fin.cons (fun y => f y ^ 2 / 2) φ) z =
          f z * maDens (Fin.cons f φ) z + gradDens φ f f z

def EnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (v : (Fin (d + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → 0 ≤ gradDens (fun _ : Fin d => euclPot ∘ s) v v y

def GradDensSheetBound.Statement : Prop :=
  ∀ (n d : ℕ) (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ)),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
        (v w : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ∈ K →
          |gradDens (fun i => φ i ∘ s) v w y| ≤
            C * Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) v v y) *
              Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) w w y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

noncomputable section

namespace HolomorphicFibreInfinite

theorem kernel_eq_of_maximal {k d r : ℕ} (A : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ)) (v : Fin r → Fin k → ℂ)
    (Λ : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hmax : ∀ u : Fin (r + 1) → Fin k → ℂ, ¬ LinearIndependent ℂ (fun j => A (u j)))
    (hind : LinearIndependent ℂ (fun j => Λ (A (v j)))) {x : Fin k → ℂ} (hx : Λ (A x) = 0) :
    A x = 0 := by
  have hv : LinearIndependent ℂ (fun j => A (v j)) := LinearIndependent.of_comp Λ hind
  by_cases hs : A x ∈ Submodule.span ℂ (Set.range fun j => A (v j))
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
    have h0 : ∑ j, c j • Λ (A (v j)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hx, ← hc, map_sum]
      simp only [map_smul]
    have hc0 := Fintype.linearIndependent_iff.1 hind c h0
    rw [← hc]
    simp [hc0]
  · exfalso
    apply hmax (Fin.cons x v)
    have hfun : (fun j => A ((Fin.cons x v : Fin (r + 1) → Fin k → ℂ) j)) =
        (Fin.cons (A x) (fun j => A (v j)) : Fin (r + 1) → Fin d → ℂ) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hfun]
    exact hv.finCons hs

theorem proof : HolomorphicFibreInfinite.Statement := by
  intro k d U f hdk hU hUne hf
  classical
  have hfa : AnalyticOnNhd ℂ f U :=
    GroundTheory.Heights₂.Heights.ImplicitCurve.analyticOnNhd_of_differentiableOn hU hf

  let Q : ℕ → Prop := fun m => ∃ t ∈ U, ∃ v : Fin m → Fin k → ℂ,
    LinearIndependent ℂ (fun j => fderiv ℂ f t (v j))
  have hQ0 : Q 0 := by
    obtain ⟨t, ht⟩ := hUne
    exact ⟨t, ht, Fin.elim0, linearIndependent_empty_type⟩
  have hspec : Q (Nat.findGreatest Q d) := Nat.findGreatest_spec (Nat.zero_le d) hQ0
  have hle : ∀ m, m ≤ d → Q m → m ≤ Nat.findGreatest Q d := fun m hmd hm => Nat.le_findGreatest hmd hm
  have hrd : Nat.findGreatest Q d ≤ d := Nat.findGreatest_le d
  generalize Nat.findGreatest Q d = r at hspec hle hrd
  obtain ⟨s, hs, v, hv⟩ := hspec
  have hmax : ∀ t ∈ U, ∀ u : Fin (r + 1) → Fin k → ℂ,
      ¬ LinearIndependent ℂ (fun j => fderiv ℂ f t (u j)) := by
    intro t ht u hu
    have hcard : r + 1 ≤ d := by simpa using hu.fintype_card_le_finrank
    have := hle (r + 1) hcard ⟨t, ht, u, hu⟩
    omega

  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Fintype.linearCombination ℂ (fun j => fderiv ℂ f s (v j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hv c (by simpa [T, Fintype.linearCombination_apply] using hc) j
  obtain ⟨Λ, hΛ⟩ := T.exists_leftInverse_of_injective hT
  have hΛv : ∀ j, Λ (fderiv ℂ f s (v j)) = Pi.single j 1 := by
    intro j
    have := congrArg (fun g => g (Pi.single j (1 : ℂ))) hΛ
    simpa [T, Fintype.linearCombination_apply_single] using this
  let Λc : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap Λ
  have hΛc : ∀ y, Λc y = Λ y := fun y => rfl

  have hev : ∀ᶠ t in 𝓝 s, t ∈ U ∧ LinearIndependent ℂ (fun j => Λ (fderiv ℂ f t (v j))) := by
    have hUev : ∀ᶠ t in 𝓝 s, t ∈ U := hU.mem_nhds hs
    refine hUev.and ?_
    have hDcont : ContinuousAt (fderiv ℂ f) s := (hfa.fderiv s hs).continuousAt
    have hc : ContinuousAt (fun t => fun j => Λc (fderiv ℂ f t (v j))) s := by
      refine continuousAt_pi.2 fun j => ?_
      exact Λc.continuous.continuousAt.comp
        ((ContinuousLinearMap.apply ℂ (Fin d → ℂ) (v j)).continuous.continuousAt.comp hDcont)
    have h0 : LinearIndependent ℂ (fun j => Λc (fderiv ℂ f s (v j))) := by
      have : (fun j => Λc (fderiv ℂ f s (v j))) = ⇑(Pi.basisFun ℂ (Fin r)) := by
        funext j
        simp [hΛc, hΛv]
      rw [this]
      exact (Pi.basisFun ℂ (Fin r)).linearIndependent
    exact hc.eventually h0.eventually

  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := Λ ∘ₗ (fderiv ℂ f s : (Fin k → ℂ) →ₗ[ℂ] (Fin d → ℂ)))
      (by simp; omega))
  have hw' : Λ (fderiv ℂ f s w) = 0 := by simpa using hw

  let A' : ℂ × (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin r → ℂ)).smulRight w +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin r → ℂ))).smulRight (v j)
  have hA' : ∀ p : ℂ × (Fin r → ℂ), A' p = p.1 • w + ∑ j, p.2 j • v j := by
    intro p
    simp [A']
  have hLA : ∀ p : ℂ × (Fin r → ℂ), Λ (fderiv ℂ f s (A' p)) = p.2 := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA', map_add (f := _), map_add (f := _), map_smul, map_smul, hw', smul_zero, zero_add, map_sum, map_sum]
    simp only [map_smul, hΛv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  let H : ℂ × (Fin r → ℂ) → Fin r → ℂ := fun p => Λc (f (s + A' p))
  have hfs : AnalyticAt ℂ f s := hfa s hs
  have hHd : HasFDerivAt H (Λc.comp ((fderiv ℂ f s).comp A')) 0 := by
    have h1 : HasFDerivAt (fun p => s + A' p) A' (0 : ℂ × (Fin r → ℂ)) := A'.hasFDerivAt.const_add s
    have h2 : HasFDerivAt f (fderiv ℂ f s) (s + A' 0) := by
      simpa using hfs.differentiableAt.hasFDerivAt
    exact Λc.hasFDerivAt.comp _ (HasFDerivAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) h2 h1)
  have hHc : ContDiffAt ℂ 1 H 0 := by
    have hf1 : ContDiffAt ℂ 1 f (s + A' 0) := by simpa using hfs.contDiffAt
    exact Λc.contDiff.contDiffAt.comp _
      (ContDiffAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) hf1 (contDiff_const.add A'.contDiff).contDiffAt)
  have hinv : (fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ)).IsInvertible := by
    have : fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ) =
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
      rw [hHd.fderiv]
      refine ContinuousLinearMap.ext fun c => ?_
      simpa [hΛc] using hLA (0, c)
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩

  have hψc := hHc.contDiffAt_implicitFunction one_ne_zero hinv
  set ψ := hHc.implicitFunction one_ne_zero hinv with hψ
  have hψ0 : ψ 0 = 0 := hHc.implicitFunction_apply_self one_ne_zero hinv
  have hψeq : ∀ᶠ z in 𝓝 (0 : ℂ), H (z, ψ z) = H 0 :=
    hHc.eventually_apply_implicitFunction one_ne_zero hinv
  have hψd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    (hψc.eventually (by simp)).mono fun z hz => hz.differentiableAt one_ne_zero
  let P : ℂ → Fin k → ℂ := fun z => s + A' (z, ψ z)
  have hP0 : P 0 = s := by simp [P, hψ0, hA']
  have hPcont : ContinuousAt P 0 :=
    continuousAt_const.add (A'.continuous.continuousAt.comp (continuousAt_id.prodMk hψc.continuousAt))
  rw [← hP0] at hev
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (((hPcont.eventually hev).and hψeq).and hψd)
  have hPd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ P z := fun z hz =>
    (differentiableAt_const _).add (A'.differentiableAt.comp z (differentiableAt_id.prodMk (hball z hz).2))
  have hPU : ∀ z ∈ ball (0 : ℂ) δ, P z ∈ U := fun z hz => (hball z hz).1.1.1
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ f (P z) := fun z hz =>
    (hf _ (hPU z hz)).differentiableAt (hU.mem_nhds (hPU z hz))
  have hgP : ∀ z ∈ ball (0 : ℂ) δ, Λc (f (P z)) = Λc (f s) := by
    intro z hz
    have := (hball z hz).1.2
    simpa [H, P] using this

  have hzero : Set.EqOn (fderiv ℂ (fun z => f (P z))) 0 (ball (0 : ℂ) δ) := by
    intro z hz
    have hcomp : fderiv ℂ (fun z => f (P z)) z = (fderiv ℂ f (P z)).comp (fderiv ℂ P z) :=
      fderiv_comp z (hfd z hz) (hPd z hz)
    have hloc : (fun z => Λc (f (P z))) =ᶠ[𝓝 z] fun _ => Λc (f s) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hgP
    have hg0 : fderiv ℂ (fun z => Λc (f (P z))) z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have hgc : fderiv ℂ (fun z => Λc (f (P z))) z = Λc.comp ((fderiv ℂ f (P z)).comp (fderiv ℂ P z)) := by
      rw [← hcomp]
      have h := fderiv_comp z Λc.differentiableAt ((hfd z hz).comp z (hPd z hz))
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hx : Λ (fderiv ℂ f (P z) (fderiv ℂ P z 1)) = 0 := by
      have := congrArg (fun L => L 1) (hgc.symm.trans hg0)
      simpa [hΛc] using this
    have := kernel_eq_of_maximal (fderiv ℂ f (P z)) v Λ (hmax _ (hPU z hz)) (hball z hz).1.1.2 hx
    rw [hcomp]
    refine ContinuousLinearMap.ext_ring ?_
    simpa using this
  have hconst : ∀ z ∈ ball (0 : ℂ) δ, f (P z) = f s := by
    intro z hz
    have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => ((hfd z hz).comp z (hPd z hz)).differentiableWithinAt) hzero hz (mem_ball_self hδ)
    simpa [hP0] using this

  have hPinj : Function.Injective P := by
    intro z z' hzz
    have hψz : ψ z = ψ z' := by
      have h1 := hLA (z, ψ z)
      have h2 := hLA (z', ψ z')
      have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
      rw [this] at h1
      exact h1.symm.trans h2
    have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
    rw [hA', hA', hψz] at this
    have h3 : z • w = z' • w := add_right_cancel this
    exact smul_left_injective ℂ hw0 h3
  refine ⟨f s, ?_⟩
  have hinf : (ball (0 : ℂ) δ).Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hδ)
  refine (hinf.image hPinj.injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨hPU z hz, hconst z hz⟩

end HolomorphicFibreInfinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

def ZeroSetOpenMass.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    ∀ (x : Fin n → ℂ) (O : Set (Fin n → ℂ)), IsOpen O → x ∈ O →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
        0 < μH[((2 * d : ℕ) : ℝ)] (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

open scoped ENNReal

noncomputable section

def ChartMassCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
        ∫⁻ y, ‖chartAbsDens J A ((Metric.closedBall 0 R).indicator g) φ y‖ₑ ≤
          K * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R},
            ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def DiscriminantSheetCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (P : MvPolynomial (Fin d) ℂ) (U D : ℕ → Set (Fin d → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin d → ℂ) → Fin n → ℂ),
        P ≠ 0 ∧
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        (⋃ k, D k)ᶜ ⊆ {y | eval y P = 0} ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre J A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt J A (s k j y) (s k j))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def weierstrassPolynomial {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (x : Option σ → ℂ) : ℂ :=
  x none ^ d + ∑ j : Fin d, c j (fun i => x (some i)) * x none ^ (j : ℕ)

theorem weierstrassPolynomial_pointWithLast_zero {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by
  have h : (fun i => pointWithLast (0 : σ → ℂ) t (some i)) = 0 := rfl
  simp only [weierstrassPolynomial, h, hc, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

def WeierstrassPreparation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (e : (Option σ → ℂ) → ℂ) (c : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ e 0 ∧ e 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (c j) 0) ∧ (∀ j, c j 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = e x * weierstrassPolynomial c x

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsSheetMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    Measurable g → (∀ k, SmoothNear (zeroSet J) (φ k)) →
      Measurable (chartDens J A g φ) ∧ Measurable (chartAbsDens J A g φ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SmallSetBallCover.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ T : Finset (Fin n → ℂ),
        (↑T : Set (Fin n → ℂ)) ⊆ zeroSet I ∩ K ∧ zeroSet I ∩ K ⊆ ⋃ c ∈ T, Metric.ball c r ∧
          (T.card : ℝ) * r ^ (2 * d) ≤ C * r ^ 2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceDim.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) =
        ((e : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarIntAdd.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin k → (Fin n → ℂ) → ℝ),
    J.IsPrime → Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J k (f + g) φ = varInt J k f φ + varInt J k g φ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def StokesOnChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    (HasCompactSupport f ∨ HasCompactSupport g) →
      chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ)

end

end GroundTheory.Heights₂.Heights
end
