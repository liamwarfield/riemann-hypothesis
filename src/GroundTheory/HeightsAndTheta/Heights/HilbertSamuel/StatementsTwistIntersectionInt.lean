module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSectionsPower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def EuclideanSectionsPower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ (m * q)))] [IsZLattice ℝ (imageLattice (φ (m * q)))],
          -Real.log (ZLattice.covolume (imageLattice (φ (m * q)))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def relChartLat {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) : Submodule R Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)}
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  zero_mem' := fun c _ => by simp
  smul_mem' := fun r s hs c hc => by rw [smul_mul_assoc]; exact Subalgebra.smul_mem _ (hs c hc) r

def RelLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n m : ℕ) (g : Fin m → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (relChartLat (Algebra.adjoin ℤ (Set.range g)) y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem secM_mul_mem (y : (Σ k, ι k) → Ω) {d e : K → ℕ} {s t : Ω} (hs : s ∈ secM y d)
    (ht : t ∈ secM y e) : s * t ∈ secM y (d + e) := by
  have hgen : ∀ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → aeval y g * t ∈ secM y (d + e) := by
    intro g hg
    change t ∈ Submodule.span ℤ _ at ht
    change _ ∈ Submodule.span ℤ _
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  change s ∈ Submodule.span ℤ _ at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hgen g hg
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul n x _ hx => rw [smul_mul_assoc]; exact zsmul_mem hx n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageMetrics
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def linPullMetric {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ)
    (hN : ∀ u : J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) : ConeMetric ℂ J where
  ρ u := (fsMetric (ι := κ)).ρ (fun i => ∑ j, (N i j : ℂ) * u j)
  pos u hu := (fsMetric (ι := κ)).pos _ fun h => hu (hN u h)
  smul c u := by
    have : (fun i => ∑ j, (N i j : ℂ) * (c • u) j) = c • fun i => ∑ j, (N i j : ℂ) * u j := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, (fsMetric (ι := κ)).smul]

def BlockImageMetrics.Statement : Prop :=
  (∀ (κ J : Type) [Fintype κ] [Fintype J] (N : Matrix κ (Ix J) ℤ)
      (hN : ∀ u : Ix J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) (P : Ideal (MRing (GlobalTheory J))),
      IsSemipositiveRel ⊥ P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (linPullMetric N hN))) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K) (P : Ideal (MRing ι)),
      IsSemipositiveRel ⊥ P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (unitDeg k₀))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageInverse.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω) (J : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y →
      ∃ (F : MvPolynomial (Ix (Fin r)) ℤ) (e : ℕ) (G : MRing ι) (dG : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e) ∧ F ∉ coordIdeal ℤ x ∧
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG ∧ G ∉ mCoordIdeal y ∧
        (∀ z, eval z (map (Int.castRingHom ℂ) G) = eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F)) ∧
        (∀ u ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x), eval u (map (Int.castRingHom ℂ) F) ≠ 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), z ∉ mcPts J ∧ SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) u) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 → z ∉ mcPts J) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), ∀ z' ∈ mcPts (mCoordIdeal y),
          eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 →
          SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) (blockMapC k₀ M z') → SameOrbit z z')

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology

theorem L1Convergence.proof : L1Convergence.Statement := by
  intro Ω _ μ _ g b C hg hb hC hlim hint

  have hp_int : ∀ n, Integrable (fun x => max (g n x - b x) 0) μ :=
    fun n => ((hg n).sub hb).pos_part
  have hbound_int : Integrable (fun x => C + |b x|) μ := (integrable_const C).add hb.abs
  have hpt : Tendsto (fun n => ∫ x, max (g n x - b x) 0 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => max (g n x - b x) 0) (f := fun _ => (0 : ℝ)) (fun x => C + |b x|)
      (fun n => (hp_int n).aestronglyMeasurable) hbound_int
      (fun n => Filter.Eventually.of_forall fun x => by
        have h1 := hC n x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [neg_abs_le (b x)]) (by linarith [abs_nonneg (b x)]))
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
          lt_of_lt_of_le ha (le_max_right _ _), fun a ha => ?_⟩
        filter_upwards [hlim x (a / 2) (by linarith)] with n hn
        exact lt_of_le_of_lt (max_le (show g n x - b x ≤ a / 2 by linarith)
          (show (0 : ℝ) ≤ a / 2 by linarith)) (by linarith))
    simpa using h

  have hid : ∀ n, ∫ x, |g n x - b x| ∂μ =
      2 * ∫ x, max (g n x - b x) 0 ∂μ - (∫ x, g n x ∂μ - ∫ x, b x ∂μ) := by
    intro n
    have hpt' : ∀ x, |g n x - b x| = 2 * max (g n x - b x) 0 - (g n x - b x) := by
      intro x
      rcases le_total 0 (g n x - b x) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    simp_rw [hpt']
    have hgb : Integrable (fun x => g n x - b x) μ := (hg n).sub hb
    rw [integral_sub ((hp_int n).const_mul 2) hgb, integral_const_mul,
      integral_sub (hg n) hb]
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (integral_nonneg fun x => abs_nonneg _), fun a ha => ?_⟩
  filter_upwards [(tendsto_order.1 hpt).2 (a / 4) (by linarith), hint (a / 4) (by linarith)]
    with n hn1 hn2
  rw [hid n]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKrullDimMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KrullDimMatAct

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def coneAdjoinQ (x : J → Ω) : Subalgebra ℚ (Polynomial Ω) :=
  Algebra.adjoin ℚ (Set.range fun j => Polynomial.C (x j) * Polynomial.X)

theorem mem_coneAdjoinQ_matAct (A : Matrix J J ℚ) (x : J → Ω) (i : J) :
    Polynomial.C (matAct A x i) * Polynomial.X ∈ coneAdjoinQ x := by
  have h : Polynomial.C (matAct A x i) * Polynomial.X =
      ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [matAct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]
  rw [h]
  exact Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _

theorem coneAdjoinQ_matAct_le (A : Matrix J J ℚ) (x : J → Ω) :
    coneAdjoinQ (matAct A x) ≤ coneAdjoinQ x :=
  Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)

theorem coneAdjoinQ_matAct_eq {B : Matrix J J ℚ} (hB : IsInvMat B) (x : J → Ω) :
    coneAdjoinQ (matAct B x) = coneAdjoinQ x := by
  classical
  obtain ⟨B', _, hB'B⟩ := isInvMat_mul hB
  refine le_antisymm (coneAdjoinQ_matAct_le B x) ?_
  have h := coneAdjoinQ_matAct_le B' (matAct B x)
  rwa [matAct_matAct hB'B] at h

theorem ringKrullDim_quot_coordIdeal (x : J → Ω) :
    ∃ s : ℕ, Algebra.trdeg ℚ (coneAdjoinQ x) = s ∧
      ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x) = (s : WithBot ℕ∞) + 1 := by
  obtain ⟨s, h1, h2⟩ := GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker
    (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)
  have hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) =
      fun j => Polynomial.C (x j) * Polynomial.X :=
    funext fun v => by simp [coneMap]
  rw [hX] at h1
  exact ⟨s, h1, h2⟩

theorem proof : KrullDimMatAct.Statement := by
  intro Ω _ _ J _ x B hB
  obtain ⟨s, hs, hds⟩ := ringKrullDim_quot_coordIdeal (matAct B x)
  obtain ⟨t, ht, hdt⟩ := ringKrullDim_quot_coordIdeal x
  rw [coneAdjoinQ_matAct_eq hB, ht] at hs
  have hst : s = t := by exact_mod_cast hs.symm
  rw [hds, hdt, hst]

end KrullDimMatAct

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace VeroneseArith

open Veronese

def sq (D : ℕ) (i : Fin (D + 1)) : Ix (Idx D) := ⟨(), ⟨(i, i), le_rfl⟩⟩

theorem sq_injective (D : ℕ) : Function.Injective (sq D) := by
  intro i j h
  have := congrArg (fun q : Ix (Idx D) => q.2.1.1) h
  simpa [sq] using this

theorem t_ne_zero (D : ℕ) (i : Fin (D + 1)) : t D i ≠ 0 := by
  rw [t, ← map_zero (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D))]
  exact (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).ne (X_ne_zero i)

theorem aeval_sq (D : ℕ) (f : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval (x D ∘ sq D) f = algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)
      (MvPolynomial.map (Int.castRingHom ℚ) (expand 2 f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hp, map_mul, map_mul, map_mul, aeval_X, expand_X, map_pow, map_X, map_pow]
    simp [x, sq, t, pow_two]

theorem coordIdeal_sq (D : ℕ) : coordIdeal ℤ (x D ∘ sq D) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot, ← sum_homogeneousComponent f]
  refine Finset.sum_eq_zero fun d _ => ?_
  have h1 : aeval (x D ∘ sq D) (homogeneousComponent d f) = 0 := by
    rw [← coeff_coneMap ℤ]
    rw [coordIdeal, RingHom.mem_ker] at hf
    rw [hf, Polynomial.coeff_zero]
  rw [aeval_sq] at h1
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) (h1.trans (map_zero _).symm)
  have h3 := MvPolynomial.map_injective _ (Int.castRingHom ℚ).injective_int (h2.trans (map_zero _).symm)
  exact (expand_eq_zero two_pos).mp h3

theorem isIntegral_coord (D : ℕ) (q : Ix (Idx D)) :
    IsIntegral (coneRing ℤ (x D ∘ sq D)) (Polynomial.C (x D q) * Polynomial.X : Polynomial (Fld D)) := by
  have hmem : ∀ i, (Polynomial.C (x D (sq D i)) * Polynomial.X : Polynomial (Fld D)) ∈
      coneRing ℤ (x D ∘ sq D) := fun i => ⟨X i, by simp [coneMap]⟩
  have hsq : (Polynomial.C (x D q) * Polynomial.X : Polynomial (Fld D)) ^ 2 =
      (Polynomial.C (x D (sq D q.2.1.1)) * Polynomial.X) * (Polynomial.C (x D (sq D q.2.1.2)) * Polynomial.X) := by
    simp only [x, sq, map_mul]
    ring
  refine IsIntegral.of_pow two_pos ?_
  rw [hsq]
  exact isIntegral_algebraMap (R := coneRing ℤ (x D ∘ sq D)) (A := Polynomial (Fld D))
    (x := ⟨_, mul_mem (hmem _) (hmem _)⟩)

theorem isProjFrame_sq (D : ℕ) : IsProjFrame (x D) (sq D) :=
  ⟨sq_injective D, coordIdeal_sq D, isIntegral_coord D⟩

theorem proof : VeroneseArith.Statement := by
  intro D _
  refine ⟨⟨()⟩, ⟨coordIdeal_isPrime ℤ _, isMultiHomogIdeal_coordIdeal _, ?_⟩, isHorizontal_coordIdeal _, ?_⟩
  · intro k
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [X_mem_coordIdeal_iff]
    exact mul_ne_zero (t_ne_zero D 0) (t_ne_zero D 0)
  · rw [ringKrullDim_quot_of_frame _ (sq D) (isProjFrame_sq D), Fintype.card_unit]

end VeroneseArith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

lemma mem_source_chartIdx (A : FinHolAtlas D X) (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

lemma target_inter_symm_source (A : FinHolAtlas D X) (j : Fin A.n) :
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
  inter_eq_left.2 fun _ hy => (A.chart j).map_target hy

theorem LocalBergmanBound.proof (hC : ChartBergmanBound.Statement) :
    LocalBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV x ε hε
  have := dV.isProb
  set k := chartIdx A x with hk
  set e := A.chart k with he
  have hx : x ∈ e.source := mem_source_chartIdx A x
  have hy0 : e x ∈ e.target := e.map_source hx
  have hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target := by
    have := W.smooth k k
    rwa [target_inter_symm_source] at this
  have hmain := hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0
    (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0)
    (fun w => hW k (e x) hy0 w) ε hε
  have hb : bergmanDens W dV x =
      (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x) := by
    have hD : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
    exact mul_div_mul_left _ _ hD
  filter_upwards [hmain] with n hn
  rw [← hb] at hn
  set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK

  have hKpos : 0 < K := by
    by_contra hle
    have h1 := hn (fun _ => 1) analyticOnNhd_const
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h1
    have : 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) := by
      simp [Real.exp_pos]
    linarith
  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV n s.2
  have hcont := continuous_ptNormSq W hs
  have hnn : ∀ z, 0 ≤ ptNormSq W n s z := ptNormSq_nonneg W n s
  have hint : Integrable (ptNormSq W n s) dV.μ := integrable_ptNormSq W dV hs
  have hl2 : 0 ≤ sectionL2NormSq W dV n s := sectionL2NormSq_nonneg W dV n s

  have hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target := by
    have := hs.1 k k
    rwa [target_inter_symm_source] at this
  have h1 := hn _ hF
  have hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x := by
    simp only [Function.comp, e.left_inv hx]
    rfl
  have hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤
        ENNReal.ofReal (sectionL2NormSq W dV n s) := by
    have hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z) :=
      hcont.measurable.ennreal_ofReal
    calc _ = ∫⁻ y in e.target, ENNReal.ofReal (ptNormSq W n s (e.symm y)) *
          ENNReal.ofReal (dV.dens k y) := by
          refine setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]
          rfl
      _ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ :=
          (dV.chart_lintegral k _ hmeas).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sectionL2NormSq W dV n s) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
  rw [hleft] at h1
  have h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s) := by
    rw [ENNReal.ofReal_mul hKpos.le]
    exact h1.trans (by gcongr)
  have h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2
  rcases hl2.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hKpos.le
  · exact (div_le_iff₀ hpos).2 h3

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenFibreHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenFibreHomog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sum_block_eq_weight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, m ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) m k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isMultiHomog_of_weighted {f : MRing ι} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  intro m hm k
  rw [sum_block_eq_weight, hf (mem_support_iff.mp hm)]

theorem coeff_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MRing ι) :
    AddMonoidAlgebra.coeff (mConeMap y f) (Finsupp.equivFunOnFinite.symm b) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm),
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]

theorem isMultiHomogIdeal_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := ℤ) (mCoordIdeal y) := by
  intro f hf b
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  change mConeMap y _ = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y
      (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)),
    ← coeff_mConeMap, hf']
  simp

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [∀ k, Fintype (ι k)] in
theorem isHomogeneous_of_isMultiHomogIdeal {R : Type} [CommRing R] {I : Ideal (MvPolynomial (Σ k, ι k) R)}
    (h : NumbersDVR.IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
  intro b f hf
  have key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b :
      MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f :=
    weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b
  rw [key]
  exact h f hf b

end GenFibreHomog


open GenFibreHomog in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem GenFibreHomog.proof : GenFibreHomog.Statement := by
  intro K _ _ ι _ Ω _ y
  have hI := isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  have hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι)) := by
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := s.2
    refine ⟨b, ?_⟩
    rw [mem_weightedHomogeneousSubmodule] at hb ⊢
    intro d hd
    apply hb
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HilbFnValueSpan

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def coneQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (coneQ y) := by
  have hring : ((coneQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MRing ι →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneQ, mConeMap]
    · intro i
      simp [coneQ, mConeMap]
  have hker : mCoordIdeal y =
      (RingHom.ker (coneQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (coneQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isWeightedHomogeneous_iff {R : Type} [CommRing R] (f : MvPolynomial (Σ k, ι k) R) (a : K → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a ↔ ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight, h m (mem_support_iff.mpr hm) k]

theorem coneQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    coneQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  have hf' := (isWeightedHomogeneous_iff f a).mp hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p =
      ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [coneQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_ker_iff (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    f ∈ RingHom.ker (coneQ y) ↔ aeval y f = 0 := by
  rw [RingHom.mem_ker, coneQ_eq y hf]
  constructor
  · intro h
    have hne : (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    rcases mul_eq_zero.mp h with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h hne
  · intro h
    rw [h, map_zero, zero_mul]

def evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] Ω :=
  (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap.comp (Submodule.subtype _)

def quotForms (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P :=
  (Ideal.Quotient.mkₐ ℚ P).toLinearMap.comp (Submodule.subtype _)

theorem range_evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    LinearMap.range (evalForms y a) = valueSpan y a := by
  apply le_antisymm
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hf' := (isWeightedHomogeneous_iff f a).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
    show aeval y f ∈ valueSpan y a
    conv => arg 2; rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    have hmon : aeval y (monomial v (AddMonoidAlgebra.coeff f v)) =
        AddMonoidAlgebra.coeff f v • aeval y (monomial v (1 : ℤ) : MRing ι) := by
      simp only [aeval_monomial, Algebra.smul_def, map_one, one_mul]
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial v 1, ?_, rfl⟩)
    intro m hm k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
    rw [hm]
    exact hf' v hv k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom ℚ) g ∈
        weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a := by
      rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]
      exact fun m hm k => hg m (support_map_subset _ _ hm) k
    refine ⟨⟨_, hmem⟩, ?_⟩
    show aeval y (MvPolynomial.map (Int.castRingHom ℚ) g) = aeval y g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem finrank_gradedPiece (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    Module.finrank ℚ (NumbersDVR.gradedPiece
        ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) a) =
      Module.finrank ℚ (valueSpan y a) := by
  set P := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hrange : LinearMap.range (quotForms P a) = NumbersDVR.gradedPiece P a := by
    rw [quotForms, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker (quotForms P a) = LinearMap.ker (evalForms y a) := by
    ext ⟨f, hf⟩
    rw [mem_weightedHomogeneousSubmodule] at hf
    simp only [LinearMap.mem_ker, quotForms, evalForms, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [show P = RingHom.ker (coneQ y) from map_mCoordIdeal y, mem_ker_iff y hf]
  rw [← hrange, ← range_evalForms y a, ← (quotForms P a).quotKerEquivRange.finrank_eq,
    ← (evalForms y a).quotKerEquivRange.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end HilbFnValueSpan

theorem HilbFnValueSpan.proof : HilbFnValueSpan.Statement := by
  intro K _ _ ι _ Ω _ _ y a
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Int.natCast_nonneg _)]
  have ha : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
  rw [ha, HilbFnValueSpan.finrank_gradedPiece]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionsAsymptotic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

set_option linter.unusedSectionVars false

section Coordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_smul_one (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y a τ = chartLatQ y ((τ : ℤ) • a) 1 := by
  ext s
  show (∀ c : ∀ k, ι k, _ → _) ↔ (∀ c : ∀ k, ι k, _ → _)
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]

end Coordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharZeroOfIsHorizontal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

theorem charZero_of_isHorizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn,
      map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem ArithmeticVolumeBig.proof (hB : G6.StatementB) (hZ : ArithmeticVolumeDegreeZero.Statement) : ArithmeticVolumeBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  by_cases hbig : 0 < genDeg (mCoordIdeal y) D A.a
  · have : CharZero Ω := charZero_of_isHorizontal y har.2.2.1
    exact hB K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, hbig⟩
  · exact hZ K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc (not_lt.mp hbig)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
