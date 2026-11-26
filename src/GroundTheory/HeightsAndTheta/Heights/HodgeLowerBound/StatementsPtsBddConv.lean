module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsPtsNull (P : Ideal (MRing ι)) (e : ℕ) (N : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} = 0

def IsPtsIntegrable (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ φ g y w)

def PtsBddConv.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ) (g₀ : ((Σ k, ι k) → ℂ) → ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (C s₀ : ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → 0 < r → IsPtsNull P e N → 0 < s₀ →
    (∀ s : ℝ, 0 < s → s < s₀ → (∀ z ∈ mcPts P, |g s z| ≤ C) ∧ ContinuousOn (g s) (mcPts P \ N) ∧
      ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, g s (torusSmul c z) = g s z) →
    (∀ z ∈ mcPts P, z ∉ N → Tendsto (fun s => g s z) (𝓝[>] 0) (𝓝 (g₀ z))) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ ∧
      Tendsto (fun s => ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀))

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.CurvePointsFinite

theorem degC_pos_of_isArithVar_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) : 0 < degC W := by
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  rw [hdeg]
  exact Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩

theorem ZhangLowerX.proof (h : SuccessiveMinimaLowerBound) : ZhangLowerX.Statement := by
  intro K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh
  refine h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_
  have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
  have h1 := hh W hW hPW
  rwa [IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd] at h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFnFieldTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FnFieldTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (d : ℕ), Birational y → IsArithVar (mCoordIdeal y) (d + 1) → Algebra.trdeg ℤ Ω = d

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem FnFieldTrdeg.full : FnFieldTrdeg.Statement := by
  intro K _ ι _ Ω _ y d hbir harith
  obtain ⟨_, ⟨hprime, _, hrel⟩, hhor, hdim⟩ := harith
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have htr := ConeTrdeg.full K ι Ω y hbir hne hhor
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 = ((d + 1 + Fintype.card K : ℕ) : ℕ∞) :=
    WithBot.coe_injective hdim
  rw [map_add (f := _), Cardinal.toENat_nat] at h1
  have h2 : (Algebra.trdeg ℤ Ω).toENat = (d : ℕ∞) := by
    have h3 : (Algebra.trdeg ℤ Ω).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      push_cast at h1 ⊢
      rw [← add_assoc, h1]; ring
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def VertFactorPos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ),
    p ∈ D.S → ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHermExtend
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def SmoothAlong {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set V) (f : V → ℝ) : Prop :=
  ∀ z ∈ S, ∃ U ∈ 𝓝 z, ∃ G : V → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U ∧ ∀ w ∈ U ∩ S, f w = G w

def HermExtend.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ)
    (F : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, 0 < F z) →
    (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z) →
    SmoothAlong (mcPts P) F →
    ∃ Z : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, Z.a = a ∧ IsSmoothHerm Z ∧ ∀ z ∈ mcPts P, Z.h z = F z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PivotMinorFlag.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n), (a : ℕ) ≤ b →
    ∃ S : PluckerBlocks n n a, pivotMinor M a b = flagMinor M a S

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def RatioFieldSpan.Statement : Prop :=
  ∀ (F M : Type) [Field F] [Field M] [Algebra F M] (I J : Type) (u : I → M) (w : J → M) (v v' : M),
    Submodule.span F (Set.range u) = Submodule.span F (Set.range w) →
    v ∈ Submodule.span F (Set.range u) → v' ∈ Submodule.span F (Set.range u) → v ≠ 0 → v' ≠ 0 →
    IntermediateField.adjoin F (Set.range fun i => u i / v) = IntermediateField.adjoin F (Set.range fun j => w j / v')

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuMeasureLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2))
        (𝓝[>] 0) (𝓝 (meanU X.H X.Cd * degMu X.H / 2)) ∧
      Tendsto (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) (𝓝[>] 0) (𝓝 (degMu X.H))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagMinorTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTTop
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTTop.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B → 1 ≤ p → p ≤ q →
      ∃ L : ℝ, Tendsto (X.topN B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarChartSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt), ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


namespace Line

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Boundary

theorem mcPts_torus {B : Ideal (MRing ι)} (hB : IsMultiHomogIdeal B) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts B)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts B := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  obtain ⟨S, hS, rfl⟩ := hB
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha⟩ := hS s hs
    rw [eval_map]
    unfold torusSmul
    rw [IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha, ← eval_map, hz.2 s (Ideal.subset_span hs),
      mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, eval_mul, hx, mul_zero]

end Boundary

section Ample

end Ample

end GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGenLeadMinorNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinorNeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMatFr F Ψ n τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBirationalRatioClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def BirationalRatioClosure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k), Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) → Subfield.closure (coneRatios y c) = ⊤

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagRatioTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagRatioTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n : ℕ),
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n))) =
      ((Fintype.card Ψ * GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.flagDim n : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TopNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ c : ℕ → ℝ → ℝ, c 0 = arLimFun X.H X.S B ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.topN B 1 q t = ∑ i ∈ Finset.range (D.n + 2), c i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg X.H X.S B t)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTVb.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∃ L : ℝ, Tendsto (X.Vb B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesStep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def stokesMixPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n i : ℕ) :
    Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

def StokesStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n i : ℕ)
    (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), IsArithVar P (n + 1) → A'.a = A.a → IsSemipositiveH P A → IsSemipositiveH P A' →
    i < n →
      ptsIntegral P (stokesMixPot A A' n (i + 1)) (fun z => Real.log (A'.h z) - Real.log (A.h z)) ≤
        ptsIntegral P (stokesMixPot A A' n i) (fun z => Real.log (A'.h z) - Real.log (A.h z))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def OmNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ v d : ℕ → ℝ → ℝ,
        v 0 = (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2)) ∧
        d 0 = (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.Vb B 1 q t = ∑ i ∈ Finset.range (D.n + 1), v i t * (1 / (q : ℝ)) ^ i ∧
          X.degN B 1 q t = ∑ i ∈ Finset.range (D.n + 1), d i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitPos.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hTel : StokesTelescope.Statement) (hNs : NbarSemipos.Statement) (hTp : StokesLimitTp.Statement)
    (hT : StokesLimitT.Statement) (hE : StokesLimitEps.Statement) : StokesLimitPos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B a hII hpos hB hAr hyp
  have hc0 : (0 : ℝ) ≤ ((D.n + 1 : ℕ) : ℝ) := by positivity

  have step : ∀ m : ℕ, ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1) ≤ X.topNLim B 1 (m + 1) := by
    intro m
    have hp : 1 ≤ 1 := le_rfl
    have hpq : 1 ≤ m + 1 := by omega
    obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq
    obtain ⟨tP, htP, hP⟩ := hpos B 1 (m + 1) hB hp hpq
    obtain ⟨tH, htH, hH⟩ := hyp 1 (m + 1) hp hpq
    obtain ⟨t₂, ht₂, hTp'⟩ := hTp II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq

    have stepT : ∀ t : ℝ, 0 < t → t ≤ min t₁ t₂ →
        ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
          ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t ≤ X.topN B 1 (m + 1) t := by
      intro t ht0 ht1
      have hNt := hN t ht0 (ht1.trans (min_le_left _ _))
      obtain ⟨hlim, hVb⟩ := hTp' t ht0 (ht1.trans (min_le_right _ _)) hNt
      have hev : ∀ᶠ t' in 𝓝[>] (0 : ℝ),
          ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
            ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t' ≤ X.topN B 1 (m + 1) t := by
        filter_upwards [Ioc_mem_nhdsGT (lt_min htP htH)] with t' ht'
        have hsP := (hP t' ht'.1 (ht'.2.trans (min_le_left _ _))).1
        have htel := hTel II Ψ K ι Ω E D O Lt X B 1 (m + 1) t t' hII hpq hsP hNt
        have hh := hH t' ht'.1 (ht'.2.trans (min_le_right _ _))
        have hdeg : geomDegMUc X.H X.S' B 1 (m + 1) t' = X.degN B 1 (m + 1) t := by
          unfold geomDegMUc ComponentSetting.degN
          congr 1
          rw [hG K ι Ω D.y D.n _ D.arith hsP.1, hG K ι Ω D.y D.n _ D.arith hNt.1]
          congr 1
          simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
          rfl
        rw [hdeg] at hh
        have e : ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) = ((D.n + 1 : ℕ) : ℝ) * (a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t := by ring
        linarith
      have hL : Tendsto (fun t' => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t') (𝓝[>] 0)
          (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vlim B 1 (m + 1) t)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
      have h1 := le_of_tendsto hL hev
      have h2 := mul_le_mul_of_nonneg_left hVb hc0
      linarith
    obtain ⟨hT1, hT2, hT3⟩ := hT II Ψ K ι Ω E D O Lt X B 1 (m + 1) hII hAr hp hpq
    have hL : Tendsto (fun t => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
        X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t) (𝓝[>] 0)
        (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hT3)).sub (tendsto_const_nhds.mul hT2)
    refine le_of_tendsto_of_tendsto hL hT1 ?_
    filter_upwards [Ioc_mem_nhdsGT (lt_min ht₁ ht₂)] with t ht using stepT t ht.1 ht.2

  obtain ⟨hE1, hE2, hE3⟩ := hE II Ψ K ι Ω E D O Lt X B hII hAr
  have hε : Tendsto (fun m : ℕ => ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Nat.cast_add, Nat.cast_one] using h0
  have hL : Tendsto (fun m : ℕ => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1)) atTop
      (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2))) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hE3)).sub
      (tendsto_const_nhds.mul hE2)
  have key := le_of_tendsto_of_tendsto' hL hE1 step
  calc ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H
      = ((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2) := by ring
    _ ≤ arLim X.H X.S B := key

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace PlueckerSpan

theorem sum_prod_mul_det_indicator {R : Type} [CommRing R] {s N : ℕ} (M : Matrix (Fin s) (Fin N) R)
    (t : Fin s → Fin N) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) *
        (Matrix.of fun a j => if c a = t j then (1 : R) else 0).det =
      (Matrix.of fun a j => M a (t j)).det := by
  classical
  have hrow : (Matrix.of fun a j => M a (t j)) =
      fun a => ∑ b, M a b • fun j => if b = t j then (1 : R) else 0 := by
    ext a j
    simp [Finset.sum_apply]
  rw [hrow]
  change _ = Matrix.detRowAlternating _
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_sum
    (fun a b => M a b • fun j => if b = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_smul_univ
    (fun a => M a (c a)) (fun a j => if c a = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
  rw [h2]
  rfl

theorem sum_prod_mul_apply_eq {Ω R E : Type} [Field Ω] [CommRing R] [Algebra Ω R] [AddCommGroup E] [Module Ω E]
    {s N : ℕ} (e : Module.Basis (Fin N) Ω E) (M : Matrix (Fin s) (Fin N) R)
    (φ : Module.Dual Ω (⋀[Ω]^s E)) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) * algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => M a (Set.powersetCard.ofFinEmbEquiv.symm T j)).det := by
  classical
  have hc : ∀ c : Fin s → Fin N, algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => if c a = Set.powersetCard.ofFinEmbEquiv.symm T j then (1 : R) else 0).det := by
    intro c
    conv_lhs => rw [← (e.exteriorPower s).sum_repr (exteriorPower.ιMulti Ω s (e ∘ c))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
    congr 2
    ext a j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Function.comp_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← sum_prod_mul_det_indicator M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem span_eq_top_of_dual {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {s N M : ℕ}
    (b : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω (⋀[Ω]^s E))
    (h : ∀ A : Fin s → Fin N, StrictMono A → ∃ a : Fin M → Ω, ∀ A' : Fin s → Fin N, StrictMono A' →
      ∑ m, a m * φ m (exteriorPower.ιMulti Ω s (b ∘ A')) = if A' = A then 1 else 0) :
    Submodule.span Ω (Set.range φ) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun ψ => ?_
  rw [← (b.exteriorPower s).sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, ha⟩ := h _ (Set.powersetCard.ofFinEmbEquiv.symm T).strictMono
  have hT : (b.exteriorPower s).coord T = ∑ m, a m • φ m := by
    refine (b.exteriorPower s).ext fun T' => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rw [ha _ (Set.powersetCard.ofFinEmbEquiv.symm T').strictMono, Finsupp.single_apply]
    have hiff : ((Set.powersetCard.ofFinEmbEquiv.symm T' : Fin s → Fin N) =
        Set.powersetCard.ofFinEmbEquiv.symm T) ↔ T' = T := by
      constructor
      · intro h'
        exact Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')
      · rintro rfl
        rfl
    by_cases hTT : T' = T
    · rw [if_pos hTT, if_pos (hiff.2 hTT)]
    · rw [if_neg hTT, if_neg (fun h' => hTT (hiff.1 h'))]
  rw [hT]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end PlueckerSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
