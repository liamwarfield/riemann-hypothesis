module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {R : Type} [CommRing R] {N : ℕ}

theorem minorIJ_eq_det (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) : minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_of_card_ne (h : Matrix (Fin N) (Fin N) R) {I J : Finset (Fin N)} (e : I.card ≠ J.card) :
    minorIJ h I J = 0 := by
  unfold minorIJ
  rw [dite_eq_right e]

theorem minorIJ_mul_of_card (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) :
    minorIJ (T * h) I J = ∑ s : GroundTheory.PAdicHodge.KSubset N k, minorIJ T I s.1 * minorIJ h s.1 J := by
  rw [minorIJ_eq_det _ _ _ k hI hJ]
  have e : (T * h).submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) =
      T.submatrix (I.orderEmbOfFin hI) id * h.submatrix id (J.orderEmbOfFin hJ) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [e, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [minorIJ_eq_det T I s.1 k hI s.2, minorIJ_eq_det h s.1 J k s.2 hJ]
  rfl

theorem minorIJ_mul (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  by_cases e : I.card = J.card
  · rw [minorIJ_mul_of_card T h I J I.card rfl e.symm]
    have h1 : ∑ I' : Finset (Fin N), minorIJ T I I' * minorIJ h I' J =
        ∑ I' ∈ Finset.univ.filter (fun I' : Finset (Fin N) => I'.card = I.card),
          minorIJ T I I' * minorIJ h I' J := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
      have hc : s.card ≠ I.card := fun hc => hs (by simp [hc])
      rw [minorIJ_of_card_ne T (Ne.symm hc), zero_mul]
    rw [h1]
    exact (Finset.sum_subtype (Finset.univ.filter fun I' : Finset (Fin N) => I'.card = I.card)
      (p := fun s : Finset (Fin N) => s.card = I.card) (fun s => by simp)
      (fun I' => minorIJ T I I' * minorIJ h I' J)).symm
  · rw [minorIJ_of_card_ne _ e]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : I.card = s.card
    · rw [minorIJ_of_card_ne h (fun h' => e (hs.trans h')), mul_zero]
    · rw [minorIJ_of_card_ne T hs, zero_mul]

theorem minorIJ_eq_zero_of_row (h : Matrix (Fin N) (Fin N) R) {I C : Finset (Fin N)} {a : Fin N} (ha : a ∈ I)
    (hz : ∀ c ∈ C, h a c = 0) : minorIJ h I C = 0 := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det h I C _ e rfl]
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    simp only [Matrix.submatrix_apply]
    refine hz _ ?_
    exact Finset.orderEmbOfFin_mem _ _ _
  · exact minorIJ_of_card_ne h e

theorem sum_mem_eq_sum_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∑ k ∈ C, f k = ∑ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.sum_map]
  rfl

theorem prod_mem_eq_prod_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∏ k ∈ C, f k = ∏ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.prod_map]
  rfl

theorem minorIJ_mul_of_support (A B : Matrix (Fin N) (Fin N) R) (I C : Finset (Fin N))
    (hz : ∀ k c, c ∈ C → k ∉ C → B k c = 0) :
    minorIJ (A * B) I C = minorIJ A I C * minorIJ B C C := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det _ I C _ e rfl, minorIJ_eq_det A I C _ e rfl, minorIJ_eq_det B C C _ rfl rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    have hy : C.orderEmbOfFin rfl y ∈ C := Finset.orderEmbOfFin_mem _ _ _
    have h1 : ∑ k, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) =
        ∑ k ∈ C, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      rw [hz k _ hy hk, mul_zero]
    rw [h1, sum_mem_eq_sum_enum C]
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ e, zero_mul]

theorem minorIJ_self_of_triangular (B : Matrix (Fin N) (Fin N) R) (hB : B.BlockTriangular id) (C : Finset (Fin N)) :
    minorIJ B C C = ∏ c ∈ C, B c c := by
  rw [minorIJ_eq_det B C C _ rfl rfl]
  have ht : (B.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).BlockTriangular id := by
    intro x y hxy
    exact hB ((C.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_upperTriangular ht, prod_mem_eq_prod_enum C (fun c => B c c)]
  rfl

theorem mem_stepCols_block {N j : ℕ} {i c : Fin N} (hj : j ≤ N) (hc : c ∈ stepCols N j i) :
    if (i : ℕ) + 1 ≤ j then N - j ≤ (c : ℕ) else (c : ℕ) < N - j := by
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  split_ifs at hc ⊢ with h
  · exact hc.1
  · omega

theorem support_stepCols {N j : ℕ} {i : Fin N} (hj : j ≤ N) (bb : Matrix (Fin N) (Fin N) R)
    (hd : IsBlockDiag j bb) (ht : bb.BlockTriangular id) (k c : Fin N) (hc : c ∈ stepCols N j i)
    (hk : k ∉ stepCols N j i) : bb k c = 0 := by
  by_cases hkc : c < k
  · exact ht hkc
  have hkc' : (k : ℕ) ≤ c := by simpa using not_lt.mp hkc
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  split_ifs at hc hk with h
  · refine hd k c fun hiff => ?_
    have : ¬ (k : ℕ) < N - j → False := fun h' => hk ⟨by omega, by omega⟩
    have h3 : (k : ℕ) < N - j := by omega
    have := hiff.mp h3
    omega
  · exact absurd (by omega) hk

theorem isBlockDiag_mul {j : ℕ} {T h : Matrix (Fin N) (Fin N) R} (hT : IsBlockDiag j T) (hh : IsBlockDiag j h) :
    IsBlockDiag j (T * h) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((a : ℕ) < N - j ↔ (k : ℕ) < N - j)
  · rw [hh k b (fun h' => hab (hk.trans h')), mul_zero]
  · rw [hT a k hk, zero_mul]

theorem support_wIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ wIdx N j) (hk : k ∉ wIdx N j) : h k c = 0 := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => ?_
  have := hiff.mp (not_le.mp hk)
  omega

theorem support_omIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ omIdx N j) (hk : k ∉ omIdx N j) : h k c = 0 := by
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => hk (hiff.mpr hc)

theorem detFac_mul {j : ℕ} (i : Fin N) {T h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) :
    detFac j i (T * h) = detFac j i T * detFac j i h := by
  unfold detFac
  rw [minorIJ_mul_of_support T h _ _ (support_wIdx hh), minorIJ_mul_of_support T h _ _ (support_omIdx hh)]
  split_ifs <;> ring

theorem minor_stepCols_eq_zero {N j : ℕ} {i : Fin N} (hj : j ≤ N) (h : Matrix (Fin N) (Fin N) R)
    (I : Finset (Fin N)) (hd : IsBlockDiag j h) (hI : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  by_cases e : I.card = (stepCols N j i).card
  · have hs : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hI ⟨e, hs⟩
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    refine minorIJ_eq_zero_of_row h ha fun c hc => hd a c fun hiff => ?_
    have hb := mem_stepCols_block hj hc
    split_ifs at has hb with h1
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      have := hiff.mp (not_le.mp has)
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      exact has (hiff.mpr hb)
  · exact minorIJ_of_card_ne h e

theorem minors_main : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N →
    (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)),
      minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧
    (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I →
      minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧
    (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id →
      minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧
    ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h →
      IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  intro R _ N j i hj
  refine ⟨minorIJ_mul, fun h I hd hI => Or.inl (minor_stepCols_eq_zero hj h I hd hI), ?_, ?_⟩
  · intro h bb I hd ht
    rw [minorIJ_mul_of_support h bb I _ (support_stepCols hj bb hd ht),
      minorIJ_self_of_triangular bb ht]
  · intro T h hT hh
    exact ⟨isBlockDiag_mul hT hh, detFac_mul i hh⟩

end GlobalTheory.CompanionTheory.Ar.PB.MinorCalc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diagonal_minor_vanishing : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N → (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)), minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧ (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I → minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧ (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id → minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧ ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h → IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main | exact GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

def selM {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin S.card) ℂ :=
  Matrix.of fun a b => if a = S.orderEmbOfFin rfl b then 1 else 0

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

def grMat (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  C + ∑ I, (w I / w I₀) • B I

def IsGrChart (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ)
    (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → h.det ≠ 0 → a ≠ 0 →
    (∀ I, IsStepRows N j i I → w I = a * minorIJ h I (stepCols N j i)) → w I₀ ≠ 0 →
      IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
        ∀ I, minorIJ (grMat C B I₀ w) I (stepCols N j i) * w I₀ = a * minorIJ h I (stepCols N j i)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (k₀ : K) (z : (Σ k, ι k) → ℂ)
    (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) (basePart M.blk z) * z ⟨k₀, m⟩

def baseMono (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∏ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ^ M.dy p k.1

def stepGap (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((BM.hom p).h z) - Real.log ((fsHerm ι (M.dy p)).h z)

def stepPh (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x : R.X) : ℝ :=
  if h : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x then stepGap M BM p h.2.choose else 0

def IsStepHyp (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  IsBlockMap κ v ∧ (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) ∧
    HoloMap R.A BM.Rb.A pr ∧
    ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))

def IsStepChart (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x y₀ : R.X) (W : Set R.X) (l : Fin BM.q)
    (H : R.X → Matrix (Fin N) (Fin N) ℂ) (D : R.X → ℂ) : Prop :=
  IsOpen W ∧ y₀ ∈ W ∧ W ⊆ R.U x ∧ (∀ y' ∈ W, pr y' ∈ BM.O l) ∧
    (∀ a b, R.A.HoloOn W fun y' => H y' a b) ∧ (∀ y' ∈ W, IsBlockDiag j (H y') ∧ (H y').det ≠ 0) ∧
    R.A.HoloOn W D ∧ (∀ y' ∈ W, D y' ≠ 0) ∧
    ∀ y' ∈ W, pr y' ∉ bdry BM.s →
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' =
        blockPot j p.2 (BM.G l p.1 (pr y')) (H y') + Real.log ‖D y'‖

def HasStepCharts (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  ∀ x y₀, y₀ ∈ R.U x → ∃ W l H D, IsStepChart M BM p κ v R pr x y₀ W l H D

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def v₀ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) := ⟨some p.1, p.2⟩

def v₁ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) :=
  if h : p.1 = k₀ then ⟨none, cast (congrArg ι h) p.2⟩ else ⟨some p.1, p.2⟩

theorem v₁_ne {k₀ : K} {p : Σ k, ι k} (h : p.1 ≠ k₀) : v₁ k₀ p = ⟨some p.1, p.2⟩ := dif_neg h

theorem v₁_self (k₀ : K) (m : ι k₀) : v₁ k₀ ⟨k₀, m⟩ = ⟨none, m⟩ := dif_pos rfl

def fstPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₀ k₀

def sndPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₁ k₀

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def normRhs (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : ℝ :=
  Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
        else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁))

def IsNormFn (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (f : RW.X → ℝ) : Prop :=
  ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F →
    M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ (fstPt k₀ (RW.lift x x)) →
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 →
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) →
    f x = normRhs M τ a F z₀ z₁ h t

def IsWChart (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e)
    (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsCompatChart RW.A ψ ∧ M.IsFrame F ∧ (∀ i, σ i ≠ i₀) ∧
    (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) ∧
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) ψ.target) ∧
    ∀ x' ∈ ψ.source, (∀ τ', IsBlockDiag j (H τ' (ψ x')) ∧ (H τ' (ψ x')).det ≠ 0) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x' x')))) ∧
      ∃ z₀ z₁ : (Σ k, ι k) → ℂ, SameOrbit z₀ (fstPt k₀ (RW.lift x' x')) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift x' x')) ∧
        ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (H τ' (ψ x')) ∧
          ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₁ (if τ' = τ then H τ (ψ x') * (1 + Matrix.single cb ca (ψ x' i₀)) else H τ' (ψ x'))

def IsWAtlas (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) : Prop :=
  HoloMap RW.A Rb.A pr ∧
    (∀ x, SameOrbit (Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) ∧
    ∀ x, ∃ ψ kb σ i₀ F H, x ∈ ψ.source ∧ IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H

def IsFibreChart {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) : Prop :=
  ∃ (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X),
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀
        (if τ' = τ then H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)) else H τ' (Fin.tail z))) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem pullback_pullback {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (P : LocPot X)
    (f : Y → X) (g : Z → Y) (r : Z → X) (hf : Continuous f) (hg : Continuous g) (hr : Continuous r) (h : f ∘ g = r) :
    (P.pullback f hf).pullback g hg = P.pullback r hr := by
  subst h
  rfl

theorem orbit_symm {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem orbit_trans {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' z'' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun q => starRingEnd ℂ (z q)

theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext q; simp [cj]

theorem cj_nonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, cj z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [cj] using hi⟩

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (cj z) (cj z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => by simpa using hc k, ?_⟩
  funext p
  simp [cj]

theorem cj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : cj z ∈ mcPts P := by
  refine ⟨cj_nonzero hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  have key : eval (cj z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
      map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [map_mul, map_prod, map_pow]
  rw [key, h, map_zero]

theorem log_sub_orbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have hP : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  rw [A.smul c z' hc, B.smul c z' hc, ← hab,
    Real.log_mul hP.ne' (A.pos z' hz).ne', Real.log_mul hP.ne' (B.pos z' hz).ne']
  ring

def conjAvg (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := Real.sqrt |A.h z * A.h (cj z)|
  pos z hz := Real.sqrt_pos.2 (abs_pos.2 (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne')
  smul c z hc := by
    have hP : 0 ≤ ∏ k, ‖c k‖ ^ A.a k :=
      Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    have e1 : cj (fun p : Σ k, ι k => c p.1 * z p) =
        fun p => (starRingEnd ℂ (c p.1)) * cj z p := by
      funext p; simp [cj]
    have hc' : ∀ k, starRingEnd ℂ (c k) ≠ 0 := fun k => by simpa using hc k
    rw [e1, A.smul c z hc, A.smul _ (cj z) hc']
    simp only [RCLike.norm_conj]
    rw [show (∏ k, ‖c k‖ ^ A.a k) * A.h z * ((∏ k, ‖c k‖ ^ A.a k) * A.h (cj z)) =
      (∏ k, ‖c k‖ ^ A.a k) ^ 2 * (A.h z * A.h (cj z)) by ring, abs_mul, abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP]

theorem conjAvg_conj (A : HermLine ι) : IsConjInvariantH (conjAvg A) := fun z => by
  change Real.sqrt |A.h (cj z) * A.h (cj (cj z))| = Real.sqrt |A.h z * A.h (cj z)|
  rw [cj_cj, mul_comm]

theorem conjAvg_log (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((conjAvg A).h z) = (Real.log (A.h z) + Real.log (A.h (cj z))) / 2 := by
  have h1 := A.pos z hz
  have h2 := A.pos _ (cj_nonzero hz)
  change Real.log (Real.sqrt |A.h z * A.h (cj z)|) = _
  rw [abs_of_pos (mul_pos h1 h2), Real.log_sqrt (mul_pos h1 h2).le, Real.log_mul h1.ne' h2.ne']

theorem conjAvg_smooth {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (conjAvg A) := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hS
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) := by
    refine contDiff_pi.2 fun q => ?_
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) q)
  have hmap : Set.MapsTo (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) S S := fun z hz => cj_nonzero hz
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h (cj z)) S :=
    hA.comp hconj.contDiffOn hmap
  have hprod := hA.mul h2
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (A.h z * A.h (cj z))) S :=
    hprod.sqrt fun z hz => (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne'
  refine hs.congr fun z hz => ?_
  change Real.sqrt |A.h z * A.h (cj z)| = _
  rw [abs_of_pos (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz)))]

theorem holoOn_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {V : Set Y}
    {G : Y → ℂ} (hG : B.HoloOn V G) : A.HoloOn (g ⁻¹' V) (G ∘ g) := by
  intro j w hw
  obtain ⟨k, hk⟩ := B.cover (g ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (g ⁻¹' (B.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hg.2 j k w hw'
  have h2 : AnalyticAt ℂ (G ∘ (B.chart k).symm) ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    refine hG k _ ⟨(B.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (B.chart k).left_inv hk]
    exact hw.2
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hg.1.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hc ((B.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : g ((A.chart j).symm w') ∈ (B.chart k).source := hw''
  simp only [Function.comp, (B.chart k).left_inv hw3]

def IsLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lift : X → X → (Σ k, ι k) → ℂ) : Prop :=
  (∀ x, IsOpen (U x)) ∧ (∀ x, x ∈ U x) ∧ (∀ x p, A.HoloOn (U x) fun y => lift x y p) ∧
  (∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)) ∧
  (∀ z ∈ mcPts P, ∃ x, SameOrbit (lift x x) z) ∧
  (∀ x x', SameOrbit (lift x x) (lift x' x') → x = x') ∧
  ∀ x, ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def chartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (chartSet S σ i)

def chartComponents (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (chartIdeal S σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_chartComponents {S : Set ((Σ k, ι k) → ℂ)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ chartComponents S σ i ↔ J ∈ (chartIdeal S σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _

def chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun q : Σ k, ι k => (X (σ.symm (Function.update i q.1 q.2)) : MvPolynomial (Fin m) ℂ)) s

def domCell (i : (k : K) → ι k) : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ i', ‖segre z i'‖ ≤ ‖segre z i‖}


open Classical in
def absLogNorm (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 then |logNormC A s z| else 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibility
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XRePot
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_pot

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isNull_compl_univ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) :
    IsNull A (Set.univ : Set X)ᶜ := by
  intro j
  simp

theorem mass_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (Q : Fin D → LocPot Re.R.X) (Φ : Fin D → LocPot S.X) (hΦ : ∀ j, IsPotential S.A (Φ j))
    (hS : ∀ j, SamePot Re.R.A Set.univ (Q j) ((Φ j).pullback Re.π Re.holo.1)) :
    mInt Re.R.A Q (fun _ => 1) = Re.deg * mInt S.A Φ (fun _ => 1) := by
  rw [← degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree Φ hΦ _ continuous_const]
  exact (mInt_congr_samePot D Re.R.X Re.R.A Set.univ Q _ _ _ (isNull_compl_univ _) hS
    (fun j x _ => isC2At_of_isPotential _ (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hΦ j)) x)
    (fun _ _ => rfl)).1

end PositivityTheory.Xgp.re_pot

theorem PositivityTheory.Xgp.t_re_pot : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  intro hE K _ ι _ D σ _ S P Re
  have href : ∀ w : Fin D → σ,
      mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := fun w =>
    PositivityTheory.Xgp.re_pot.mass_eq Re _ _ (fun j => (S.sing (w j)).1) fun j => Re.ref_pot (w j)
  refine ⟨fun a t h0 h1 => PositivityTheory.Xgp.re_pot.samePot_line Re a t h0 h1, fun w => ?_, fun w t ht => ?_,
    fun n => ?_⟩
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith fun j => Re.ref_smooth (w j)]
    exact href w
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith
        fun j => Re.line_smooth (w j) (t j) (ht j).1 (ht j).2,
      PositivityTheory.Xgp.re_pot.mass_eq Re _ (fun j => S.potT (w j) (t j))
        (fun j => (anSys_open_basics D σ S).2.2.2.1 (w j) (t j) (ht j).1 (ht j).2)
        fun j => PositivityTheory.Xgp.re_pot.samePot_line Re (w j) (t j) (ht j).1 (ht j).2]
    congr 1
    exact massIndep S.A (fun j => S.th (w j)) (fun j => S.phT (w j) (t j)) (fun j => (S.sing (w j)).1)
      fun j => ((S.reg (w j)).2.2 (t j) (ht j).1 (ht j).2).1
  · have hsm : IsSmoothHerm (combLine Re.ref n) := by
      rw [combLine_eq_top]
      exact (RootFieldNumerics.combLine_smooth_conj_invariant K ι σ Re.ref n).1 Re.ref_smooth
    refine ⟨hsm, ?_⟩
    have hQ : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a =>
      isPotential_potOf Re.R (Re.ref_smooth a)
    have h1 : ReciprocityTheory.ChartRestriction.G.Geo.geomDeg P (combLine Re.ref n) D =
        mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) :=
      ptsIntegral_one_eq_mInt hE resBridge Re.R (L := fun _ => combLine Re.ref n) Re.arith fun _ => hsm
    have h2 : mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) =
        mInt Re.R.A (fun _ : Fin D => sumPot (fun a => (n a : ℝ)) fun a => potOf Re.R (Re.ref a))
          (fun _ => 1) := by
      refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr Re.R.A (locDens_congr_of_eqOn Re.R fun _ x y hy => ?_) fun _ => rfl
      have hz := (Re.R.mem x y hy).1
      show Real.log (∏ a, (Re.ref a).h (Re.R.lift x y) ^ n a) =
        ∑ a, (n a : ℝ) * Real.log ((Re.ref a).h (Re.R.lift x y))
      rw [Real.log_prod fun a _ => zpow_ne_zero _ ((Re.ref a).pos _ hz).ne']
      exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
    have h3 := (mInt_sumPot_expand D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a))
      (fun _ a => (n a : ℝ)) (fun _ => 1) (PositivityTheory.Xgp.re_pot.isNull_compl_univ _)
      (fun a x _ => PositivityTheory.Xgp.re_pot.isC2At_of_isPotential _ (hQ a) x)
      fun w => mIntegrableCont Re.R.A _ (fun j => hQ (w j)) _ continuous_const).2
    rw [h1, h2, h3, AnSys.degPoly, (formPoly_isHomogeneous_and_eval σ D S.degNum).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [href w]
    ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibility
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem re_pot : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly :=
  @PositivityTheory.Xgp.t_re_pot

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_potential_degree_compatibility : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.re_pot | exact GlobalTheory.CompanionTheory.Ar.PB.re_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.re_pot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

abbrev PartialFlagBlocks (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Type :=
  {k : K // (∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k}

instance (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Fintype (PartialFlagBlocks M p) := Fintype.ofFinite _

abbrev stepIdx (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : PartialFlagBlocks M p → Type := fun k => ι k.1

def stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : (Σ k, stepIdx M p k) → Σ k, ι k :=
  fun q => ⟨q.1.1, q.2⟩

theorem isBlockMap_stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) :
    IsBlockMap (Subtype.val : PartialFlagBlocks M p → K) (stepV M p) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨k, hk⟩, m⟩ ⟨⟨k', hk'⟩, m'⟩ h
    simp only [stepV, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    cases h2
    rfl
  · rintro ⟨k, m⟩ ⟨k', rfl⟩
    exact ⟨⟨k', m⟩, rfl⟩

theorem mem_range_step (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K) :
    k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) ↔
      ((∀ p', M.blk p' ≠ some k) ∨ ∃ p', p' = p ∧ M.blk p' = some k) := by
  constructor
  · rintro ⟨⟨k', hk'⟩, rfl⟩
    rcases hk' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p, rfl, h⟩
  · rintro (h | ⟨p', rfl, h⟩)
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · exact ⟨⟨k, Or.inr h⟩, rfl⟩

def IsStepMember {M : FlagModel y Ψ N j} {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (p : Ψ × Fin N) (ph : R.X → ℝ)
    (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y))
      (potOf R (fsHerm ι (M.dy p))) ph C₅ ∧
    IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1)
      (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ι (M.dy p))) ph phT C t₀ ∧
    IsRegFamilyC2 R.A (fun x y => BM.s (pr x) (pr y)) ph phT ∧
    (∀ t, (line t).a = M.dy p) ∧
    (∀ t, M.OnStep p (line t)) ∧
    (∀ t, 0 < t → t ≤ t₀ → IsSmoothHerm (line t) ∧ ∀ x, Real.log ((line t).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + phT t x) ∧
    (∀ x, pr x ∉ bdry BM.s → Real.log ((BM.hom p).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + ph x) ∧
    (∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) →
        ph x = ph x' ∧ ∀ t, phT t x = phT t x') ∧
    ((p.2 : ℕ) + 1 = N → ∀ t, IsPsh R.A ((potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
      IsPsh R.A (potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)) ∧ phT t = ph)

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystem
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.PfCoordOfSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig


open ReciprocityTheory.ChartRestriction.G.AI.I2 in
theorem pfCoord_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  rintro ⟨II, hSys, -, hPF, -⟩
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hL'
  have hU : UniqueStatement :=
    GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd hP (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι _)
    · exact h
  have hL's : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.isSmoothHerm_pull hv (hL j) (hL' j)
  have e1 : I K' ι' (mCoordIdeal y) d L' = II K' ι' (mCoordIdeal y) d L' :=
    hU K' ι' (I K' ι') (II K' ι') (IsIntersectionFamily.isRFamily (hI K' ι'))
      (IsIntersectionFamily.isRFamily (hSys K' ι')) _ d L' hd hP' hL's
  have e2 : I K ι (imageZ v (mCoordIdeal y)) d L = II K ι (imageZ v (mCoordIdeal y)) d L :=
    hU K ι (I K ι) (II K ι) (IsIntersectionFamily.isRFamily (hI K ι))
      (IsIntersectionFamily.isRFamily (hSys K ι)) _ d L hd hP hL
  rw [e1, e2]
  exact hPF K ι K' ι' κ v Ω y d L L' hv hP' hP hL hL'

theorem pfCoord : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement :=
  pfCoord_of_system

end PositivityTheory.HtPt.Aig
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  first | exact @PositivityTheory.HtPt.Aig.pfCoord | exact PositivityTheory.HtPt.Aig.pfCoord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystemStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_projection_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system | exact GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system | (intros; apply GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPoints
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPoints
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem resolution_onto_complex_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
  @PositivityTheory.UnitarySelfGeneration.r_onto

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPointsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_covers_complex_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points | exact GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points <;> assumption)
end
end
