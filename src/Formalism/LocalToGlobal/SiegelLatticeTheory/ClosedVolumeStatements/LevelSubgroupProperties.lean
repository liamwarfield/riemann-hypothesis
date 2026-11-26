module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsProj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.ComplexDoubleCoset
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatCountG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesMemLp
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoincareSeriesMeasurability.FoldL2DoubleCoset
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PI.PoincareSeriesMemLp.UnitaryGroupMassFormula

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem measurable_poinc {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (D : Set G) [Countable D] (Ph : G → ℂ) (hPh : Measurable Ph)
    (hs : ∀ x, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) ≠ ⊤) : Measurable (poinc D Ph) := by
  have hsum : ∀ x, Summable (fun δ : D => Ph ((δ : G) * x)) := by
    intro x
    have h1 : Summable (fun δ : D => ‖Ph ((δ : G) * x)‖₊) := by
      have h2 := hs x
      simp only [enorm_eq_nnnorm] at h2
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h1)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset D))
    (f := fun (s : Finset D) x => ∑ δ ∈ s, Ph ((δ : G) * x)) (fun s => ?_) ?_
  · exact Finset.measurable_sum _ (fun δ _ => hPh.comp (measurable_const_mul _))
  · rw [tendsto_pi_nhds]
    intro x
    unfold poinc
    exact (hsum x).hasSum

theorem fold_L2_double_coset (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesMemLp G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hdat F hF hI D hD FΓ hFΓ
  obtain ⟨hPh, hinv, hrep⟩ := hdat
  have hcΓ : Countable Γ :=
    (TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance
  have hcD : Countable D := by
    have hinj : Function.Injective (fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) := by
      intro d e h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    exact hinj.countable
  obtain ⟨hm1, hmtop, hminv, hmmeas⟩ := overlapMultiplicityProperties G Γ hΓ Ω hΩ h1

  have hqI : quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
    unfold quotientLIntegral multiplicityLIntegral
    exact lintegral_mono fun y => le_mul_of_one_le_left (by simp) (hm1 y)
  have hq : quotientLIntegral μ F Ph < ⊤ := lt_of_le_of_lt hqI hI

  have hT : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph :=
    fun x => foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.measurableSet a Ph hPh hinv hrep F hF D hD x
  have hTfin : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hmtop x).ne) hq.ne) (hT x)
  set g : G → ℝ≥0∞ := fun y => mult Γ Ω y * ‖Ph y‖ₑ with hgdef
  have hpt : ∀ x : G, ‖poinc D Ph x‖ₑ ^ 2
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) := by
    intro x
    have hP : ‖poinc D Ph x‖ₑ ≤ ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := enorm_tsum_le_tsum_enorm
    have hg : ∑' δ : D, g ((δ : G) * x) = mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun δ => ?_
      simp only [hgdef]
      rw [hminv δ (hD.1 δ.2) x]
    rw [hg, pow_two]
    calc ‖poinc D Ph x‖ₑ * ‖poinc D Ph x‖ₑ
        ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := mul_le_mul' hP hP
      _ ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ((a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph) :=
          mul_le_mul' le_rfl (hT x)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * (mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) := by ring

  have hgm : Measurable g := hmmeas.mul hPh.enorm
  have hginv : ∀ s ∈ S, ∀ y : G, g (s * y) = g y := by
    intro s hs y
    simp only [hgdef]
    rw [hminv s (hSΓ hs) y, hinv s hs y]
  have hunf : (∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ) = multiplicityLIntegral μ Γ Ω F Ph :=
    lintegralTransversalSum G μ Γ S hSΓ F hF FΓ hFΓ D hD g hgm hginv
  have hbound : (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by
    calc (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
        ≤ ∫⁻ x in FΓ, (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_mono hpt
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hq.ne)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by rw [hunf]

  have hlast : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph
      ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2 := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' le_rfl hqI) le_rfl

  have hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq) hI
  have hPm : Measurable (poinc D Ph) := measurable_poinc D Ph hPh hTfin
  refine ⟨?_, hbound, hlast⟩
  change eLpNorm (poinc D Ph) 2 (μ.restrict FΓ) < ∞
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num)
    hPm.aestronglyMeasurable]
  have h2 : ∀ x, ‖poinc D Ph x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ‖poinc D Ph x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
    norm_num
  simp_rw [h2]
  exact lt_of_le_of_lt hbound hfin

end PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
end
end

theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ :=
  PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset G μ
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesFinite
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.PoincareSeriesFinite.UnitaryGroupMassFormula

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem quotientLIntegral_le_multiplicityLIntegral {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G) (Ω : Set G)
    (h1 : (1 : G) ∈ Ω) (F : Set G) (Ph : G → ℂ) :
    quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
  unfold quotientLIntegral multiplicityLIntegral
  refine lintegral_mono fun y => ?_
  calc ‖Ph y‖ₑ = 1 * ‖Ph y‖ₑ := (one_mul _).symm
    _ ≤ mult Γ Ω y * ‖Ph y‖ₑ := by
      gcongr
      exact PI.FoldMult.UnitaryGroupMassFormula.one_le_mult Γ Ω h1 y

theorem poincareSeriesFinite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesFinite G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hPh F hF hL D hD x
  haveI := hΓ
  refine lt_of_le_of_lt (foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.isClosed.measurableSet a Ph hPh.1 hPh.2.1
    hPh.2.2 F hF D hD x) ?_
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top Γ Ω hΩ x)) ?_
  exact lt_of_le_of_lt (quotientLIntegral_le_multiplicityLIntegral μ Γ Ω h1 F Ph) hL

end PI.PoincareSeriesFinite.UnitaryGroupMassFormula
end
end

theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpTri
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange
open Finset

noncomputable section

namespace PI.ET

theorem euclTri : EuclTri := by
  intro n a b
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

theorem abel_nat (a c : ℕ → ℝ) : ∀ (n : ℕ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c i) → ∀ t : ℝ, (∀ i < n, t ≤ a i) →
    t * ∑ i ∈ range n, c i ≤ ∑ i ∈ range n, a i * c i := by
  intro n
  induction n with
  | zero => intro _ _ t _; simp
  | succ n ih =>
    intro ha hc t ht
    have ih' := ih (fun i j hij hj => ha i j hij (by omega)) (fun k hk => hc k (by omega)) (a n)
      (fun i hi => ha i n hi.le (by omega))
    have hS : 0 ≤ ∑ i ∈ range (n + 1), c i := hc (n + 1) le_rfl
    have htn : t ≤ a n := ht n (by omega)
    rw [Finset.sum_range_succ] at hS ⊢
    rw [Finset.sum_range_succ]
    nlinarith

theorem psum_eq_range {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    psum f k = ∑ i ∈ range k, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  unfold psum
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin n, (if i.val < k then f i else 0) =
      ∑ i : Fin n, (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) i.val := by
    apply Finset.sum_congr rfl; intro i _; simp [i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun m => if m < k then (if h : m < n then f ⟨m, h⟩ else 0) else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem sum_eq_range {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i ∈ range n, (fun m => if h : m < n then f ⟨m, h⟩ else 0) i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i _; simp [i.isLt]

theorem abelSq : AbelSq := by
  intro n a b ha hk htot

  set a' : ℕ → ℝ := fun m => if h : m < n then a ⟨m, h⟩ else 0 with ha'
  set c' : ℕ → ℝ := fun m => if h : m < n then (b ⟨m, h⟩ - a ⟨m, h⟩) else 0 with hc'
  have hc : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c' i := by
    intro k hkn
    have := hk k hkn
    rw [psum_eq_range a k hkn, psum_eq_range b k hkn] at this
    have e : ∑ i ∈ range k, c' i = ∑ i ∈ range k, (fun m => if h : m < n then b ⟨m, h⟩ else 0) i -
        ∑ i ∈ range k, (fun m => if h : m < n then a ⟨m, h⟩ else 0) i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro m _
      simp only [hc']; split_ifs <;> simp
    linarith
  have hmono : ∀ i j, i ≤ j → j < n → a' j ≤ a' i := by
    intro i j hij hj
    simp only [ha', dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    exact ha (show (⟨i, lt_of_le_of_lt hij hj⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  set t : ℝ := -∑ i ∈ range n, |a' i| with ht
  have htle : ∀ i < n, t ≤ a' i := by
    intro i hi
    have : |a' i| ≤ ∑ i ∈ range n, |a' i| :=
      Finset.single_le_sum (f := fun i => |a' i|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hi)
    have := neg_abs_le (a' i)
    linarith
  have key := abel_nat a' c' n hmono hc t htle
  have hc0 : ∑ i ∈ range n, c' i = 0 := by
    have e1 : ∑ i, (b i - a i) = 0 := by rw [Finset.sum_sub_distrib, htot]; ring
    rw [sum_eq_range (fun i => b i - a i)] at e1
    rw [← e1]
  rw [hc0, mul_zero] at key
  have hab : 0 ≤ ∑ i, a i * (b i - a i) := by
    rw [sum_eq_range (fun i => a i * (b i - a i))]
    convert key using 2 with m
    simp only [ha', hc']; split_ifs <;> simp
  have h1 : ∑ i, a i ^ 2 ≤ ∑ i, a i * b i := by
    have : ∑ i, a i * (b i - a i) = ∑ i, a i * b i - ∑ i, a i ^ 2 := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    linarith
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have x0 := Real.sqrt_nonneg (∑ i, a i ^ 2)
  have y0 := Real.sqrt_nonneg (∑ i, b i ^ 2)
  have hx := Real.sq_sqrt hA
  have hy := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)),
    mul_nonneg x0 y0]

end PI.ET
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
open Matrix Finset

noncomputable section

namespace PI.ET

theorem specExists : SpecExists := by
  intro n A hA
  have hH : A.IsHermitian := hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hH.eigenvectorUnitary.2
  have hspec := hH.spectral_theorem
  set l : Fin n → ℝ := hH.eigenvalues with hl

  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => OrderDual.toDual (l i))
  have hmono : Monotone ((fun i => OrderDual.toDual (l i)) ∘ σ) := Tuple.monotone_sort _
  refine ⟨l ∘ σ, fun i j hij => hmono hij, U.submatrix id σ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hUU, Matrix.submatrix_id_id]
  · have hD : Matrix.diagonal (fun i => ((l ∘ σ) i : ℂ)) =
        (Matrix.diagonal (fun i => (l i : ℂ))).submatrix σ σ := by
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    conv_lhs => rw [hspec]
    rfl

theorem hsEq : HSEq := by
  intro n A d ⟨_, W, hW, hA⟩
  have hWW : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').1 hW
  rw [Matrix.star_eq_conjTranspose] at hWW
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ) with hD
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Pi.star_apply, Complex.star_def]
  have hAh : Aᴴ = W * D * Wᴴ := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh,
      Matrix.mul_assoc]
  have key : (A * Aᴴ).trace = ∑ i, ((d i : ℂ)) ^ 2 := by
    rw [hAh, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hWW, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [sq]
  have lhs : (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have := lhs.symm.trans key
  exact_mod_cast this

end PI.ET
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
open Matrix Finset

noncomputable section

namespace PI.ET

theorem expTri_of (hS : SpecExists) (hHS : HSEq) (hH : Horn) (hA : AbelSq) (hE : EuclTri) :
    PI.ExpTri := by
  unfold PI.ExpTri
  intro n X Y Z U hX hY hZ hU hexp
  obtain ⟨ξ, hξ⟩ := hS n X hX
  obtain ⟨η, hη⟩ := hS n Y hY
  obtain ⟨ζ, hζ⟩ := hS n Z hZ
  obtain ⟨hmaj, hsum⟩ := hH n X Y Z U ξ η ζ hξ hη hζ hU hexp
  have hζ' := hζ
  obtain ⟨hanti, -⟩ := hζ'

  have hsq : ∑ i, ζ i ^ 2 ≤ ∑ i, (ξ i + η i) ^ 2 :=
    hA n ζ (fun i => ξ i + η i) hanti hmaj hsum
  rw [hHS n Z ζ hζ, hHS n X ξ hξ, hHS n Y η hη]
  exact le_trans (Real.sqrt_le_sqrt hsq) (hE n ξ η)

end PI.ET
end
end

namespace PI.ET

theorem expTri_of_horn (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri

end PI.ET
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
open Matrix Finset
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace PI.ET

namespace HornW

variable {n : ℕ}

lemma unit_star_mul {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    Wᴴ * W = 1 := by
  exact Unitary.star_mul_self_of_mem hW

lemma unit_mul_star {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    W * Wᴴ = 1 := by
  exact Unitary.mul_star_self_of_mem hW

lemma conj_mul_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d e : Fin n → ℂ) :
    (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ) = W * diagonal (fun i => d i * e i) * Wᴴ := by
  calc (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ)
      = W * (diagonal d * (Wᴴ * W) * diagonal e) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = W * diagonal (fun i => d i * e i) * Wᴴ := by
      rw [unit_star_mul hW, Matrix.mul_one, diagonal_mul_diagonal]

lemma conj_herm (W : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℝ) :
    (W * diagonal (fun i => (r i : ℂ)) * Wᴴ)ᴴ = W * diagonal (fun i => (r i : ℂ)) * Wᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext i
  rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

lemma exp_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    NormedSpace.exp (W * diagonal (fun i => (d i : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ := by
  have hinv : W⁻¹ = Wᴴ := Matrix.inv_eq_left_inv (unit_star_mul hW)
  have hu : IsUnit W :=
    (Matrix.isUnit_iff_isUnit_det W).mpr (Matrix.isUnit_det_of_right_inverse (unit_mul_star hW))
  rw [← hinv, Matrix.exp_conj W _ hu, Matrix.exp_diagonal, Pi.exp_def]
  congr 3
  funext i
  rw [Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]

lemma sq_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) *
        (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (2 * d i) : ℂ)) * Wᴴ := by
  rw [conj_mul_conj hW]
  congr 3
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add, two_mul]

lemma det_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℂ) :
    (W * diagonal d * Wᴴ).det = ∏ i, d i := by
  have h : W.det * Wᴴ.det = 1 := by rw [← Matrix.det_mul, unit_mul_star hW, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h

lemma norm_det_conj_exp {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℝ) :
    ‖(W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ).det‖ = Real.exp (∑ i, d i) := by
  rw [det_conj hW, norm_prod, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

def emb {k : ℕ} (hk : k ≤ n) : Matrix (Fin n) (Fin k) ℂ :=
  Matrix.of fun i j => if i = Fin.castLE hk j then 1 else 0

lemma emb_compress {k : ℕ} (hk : k ≤ n) (f : Fin n → ℂ) :
    (emb hk)ᴴ * diagonal f * emb hk = diagonal (fun i => f (Fin.castLE hk i)) := by
  ext i j
  simp only [emb, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, diagonal_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, (Fin.castLE_injective hk).eq_iff]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]

lemma emb_isom {k : ℕ} (hk : k ≤ n) : (emb hk)ᴴ * emb hk = 1 := by
  have h := emb_compress hk (fun _ => 1)
  simpa [Matrix.diagonal_one] using h

lemma compress_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) {k : ℕ}
    (hk : k ≤ n) (f : Fin n → ℂ) :
    (W * emb hk)ᴴ * (W * diagonal f * Wᴴ) * (W * emb hk) =
      diagonal (fun i => f (Fin.castLE hk i)) := by
  rw [conjTranspose_mul]
  calc (emb hk)ᴴ * Wᴴ * (W * diagonal f * Wᴴ) * (W * emb hk)
      = (emb hk)ᴴ * ((Wᴴ * W) * diagonal f * (Wᴴ * W)) * emb hk := by simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => f (Fin.castLE hk i)) := by
      rw [unit_star_mul hW, Matrix.one_mul, Matrix.mul_one, emb_compress]

lemma psum_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    psum f k = ∑ i : Fin k, f (Fin.castLE hk i) := by
  unfold psum
  symm
  apply Finset.sum_nbij (fun i : Fin k => Fin.castLE hk i)
  · intro a _
    simp [a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hk h
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb
    exact ⟨⟨b.val, hb⟩, by simp, Fin.ext (by simp)⟩
  · intro a _
    rfl

lemma psum_add (k : ℕ) (f g : Fin n → ℝ) :
    psum (fun i => f i + g i) k = psum f k + psum g k := by
  simp only [psum, Finset.sum_add_distrib]

lemma norm_det_diag_exp {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ‖(diagonal (fun i : Fin k => (Real.exp (2 * f (Fin.castLE hk i)) : ℂ))).det‖ =
      Real.exp (2 * psum f k) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]

lemma prod_exp_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∏ i : Fin k, Real.exp (2 * f (Fin.castLE hk i)) = Real.exp (2 * psum f k) := by
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]

lemma anti_exp {d : Fin n → ℝ} (hd : Antitone d) : Antitone (fun i => Real.exp (2 * d i)) :=
  fun i j hij => Real.exp_le_exp.mpr (by have := hd hij; linarith)

lemma isUnit_conj_exp {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℝ) : IsUnit (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ).det := by
  rw [det_conj hW]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

private lemma key_lemma' {k : ℕ} (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ∃ (V : Matrix (Fin n) (Fin k) ℂ) (P : Matrix (Fin k) (Fin k) ℂ), Vᴴ * V = 1 ∧ B = V * P := by
  have hG : (Bᴴ * B).PosDef := Matrix.PosDef.conjTranspose_mul_self B hB
  have hspec := hG.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU1 := Unitary.star_mul_self_of_mem hG.1.eigenvectorUnitary.2
  have hU2 := Unitary.mul_star_self_of_mem hG.1.eigenvectorUnitary.2
  simp only [Matrix.star_eq_conjTranspose] at hspec hU1 hU2
  have hg : ∀ i, 0 < hG.1.eigenvalues i := hG.eigenvalues_pos
  set U : Matrix (Fin k) (Fin k) ℂ := (hG.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set g := hG.1.eigenvalues with hgdef
  let s : Fin k → ℂ := fun i => (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ)
  let t : Fin k → ℂ := fun i => ((Real.sqrt (g i) : ℝ) : ℂ)
  have hst : (fun i => s i * t i) = fun _ => (1 : ℂ) := by
    funext i
    simp only [s, t]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hg i)).ne', Complex.ofReal_one]
  have hsgs : (fun i => star s i * (RCLike.ofReal ∘ g) i * s i) = fun _ => (1 : ℂ) := by
    funext i
    have hs := Real.sqrt_pos.mpr (hg i)
    have hsq : Real.sqrt (g i) * Real.sqrt (g i) = g i := Real.mul_self_sqrt (hg i).le
    simp only [s, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    have key : (Real.sqrt (g i))⁻¹ * g i * (Real.sqrt (g i))⁻¹ = 1 := by
      rw [mul_comm _ (g i), mul_assoc, ← mul_inv, hsq, mul_inv_cancel₀ (hg i).ne']
    show (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) * ((g i : ℝ) : ℂ) * (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key, Complex.ofReal_one]
  refine ⟨B * U * diagonal s, diagonal t * Uᴴ, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (diagonal s)ᴴ * (Uᴴ * Bᴴ) * (B * U * diagonal s)
        = (diagonal s)ᴴ * (Uᴴ * (Bᴴ * B) * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = (diagonal s)ᴴ * ((Uᴴ * U) * diagonal (RCLike.ofReal ∘ g) * (Uᴴ * U)) * diagonal s := by
          rw [hspec]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
            diagonal_mul_diagonal, hsgs, diagonal_one]
  · calc B = B * (U * Uᴴ) := by rw [hU2, Matrix.mul_one]
      _ = B * U * diagonal (fun i => s i * t i) * Uᴴ := by
          rw [hst, diagonal_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = B * U * diagonal s * (diagonal t * Uᴴ) := by
          rw [← diagonal_mul_diagonal]; simp only [Matrix.mul_assoc]

private lemma inv_smul_apply_smul_eq_of_smul_mem (hK : KyFanDet) {k : ℕ} (hk : k ≤ n) {p : Fin n → ℝ} (hp : Antitone p)
    (hp0 : ∀ i, 0 < p i) {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ‖(Bᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * B).det‖ ≤
      (∏ i : Fin k, p (Fin.castLE hk i)) * ‖(Bᴴ * B).det‖ := by
  obtain ⟨V, P, hV, rfl⟩ := key_lemma' B hB
  have h := hK n k hk p W V hp hp0 hW hV
  have e1 : (V * P)ᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * (V * P) =
      Pᴴ * (Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V) * P := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have e2 : (V * P)ᴴ * (V * P) = Pᴴ * P := by
    rw [conjTranspose_mul]
    calc Pᴴ * Vᴴ * (V * P) = Pᴴ * (Vᴴ * V) * P := by simp only [Matrix.mul_assoc]
      _ = Pᴴ * P := by rw [hV, Matrix.mul_one]
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, norm_mul]
  have h0 : 0 ≤ ‖Pᴴ.det‖ * ‖P.det‖ := by positivity
  calc ‖Pᴴ.det‖ * ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * ‖P.det‖
      = ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * (‖Pᴴ.det‖ * ‖P.det‖) := by ring
    _ ≤ (∏ i : Fin k, p (Fin.castLE hk i)) * (‖Pᴴ.det‖ * ‖P.det‖) :=
        mul_le_mul_of_nonneg_right h h0

private lemma key_lemma_3 {k : ℕ} {B : Matrix (Fin n) (Fin k) ℂ} (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * B = 1) : Function.Injective B.mulVec := by
  intro x y hxy
  have h1 := congrArg L.mulVec hxy
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] at h1
  exact h1

lemma key (hK : KyFanDet) {Wx Wy Wz : Matrix (Fin n) (Fin n) ℂ}
    (hWx : Wx ∈ unitaryGroup (Fin n) ℂ) (hWy : Wy ∈ unitaryGroup (Fin n) ℂ)
    (hWz : Wz ∈ unitaryGroup (Fin n) ℂ) {ξ η ζ : Fin n → ℝ} (hξ : Antitone ξ) (hη : Antitone η)
    (hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) *
        (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) =
      (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) *
        ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) *
          (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) *
        (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))
    (k : ℕ) (hk : k ≤ n) :
    psum ζ k ≤ psum (fun i => ξ i + η i) k := by
  have hV : (Wz * emb hk)ᴴ * (Wz * emb hk) = 1 := by
    rw [conjTranspose_mul]
    calc (emb hk)ᴴ * Wzᴴ * (Wz * emb hk) = (emb hk)ᴴ * (Wzᴴ * Wz) * emb hk := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [unit_star_mul hWz, Matrix.mul_one, emb_isom]
  have hinj : Function.Injective ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)).mulVec := by
    apply key_lemma_3 ((Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹)
    calc (Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ (isUnit_conj_exp hWy η), Matrix.mul_one, hV]
  have hA : ‖((Wz * emb hk)ᴴ * ((Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) * (Wz * emb hk)).det‖ = Real.exp (2 * psum ζ k) := by
    rw [sq_conj hWz, compress_conj hWz hk, norm_det_diag_exp hk]
  rw [hcc] at hA
  have e1 : (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) =
      ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e1, sq_conj hWx] at hA
  have h2 := inv_smul_apply_smul_eq_of_smul_mem hK hk (anti_exp hξ) (fun i => Real.exp_pos _) hWx _ hinj
  rw [hA] at h2
  have e2 : ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e2, sq_conj hWy] at h2
  have h3 := hK n k hk _ Wy (Wz * emb hk) (anti_exp hη) (fun i => Real.exp_pos _) hWy hV
  rw [prod_exp_eq hk] at h2
  rw [prod_exp_eq hk] at h3
  have h4 : Real.exp (2 * psum ζ k) ≤ Real.exp (2 * psum ξ k) * Real.exp (2 * psum η k) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
  rw [← Real.exp_add, Real.exp_le_exp] at h4
  rw [psum_add]
  linarith

end HornW


open HornW in
theorem horn_of (hK : KyFanDet) : Horn := by
  intro n X Y Z U ξ η ζ hX hY hZ hU hE
  obtain ⟨hξ, Wx, hWx, rfl⟩ := hX
  obtain ⟨hη, Wy, hWy, rfl⟩ := hY
  obtain ⟨hζ, Wz, hWz, rfl⟩ := hZ
  rw [HornW.exp_conj hWx, HornW.exp_conj hWy, HornW.exp_conj hWz] at hE
  have hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by
    have h1 : ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) = (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ))ᴴ * (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) := by rw [hE]
    rw [conjTranspose_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conjTranspose_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), HornW.conj_herm, HornW.conj_herm, HornW.conj_herm] at h1
    calc (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Uᴴ * U) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) := by rw [HornW.unit_star_mul hU, Matrix.mul_one]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨fun k hk => HornW.key hK hWx hWy hWz hξ hη hcc k hk, ?_⟩
  have hd : ‖((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)).det‖ = ‖(U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)).det‖ := by rw [hE]
  have hUd : ‖U.det‖ = 1 := by
    have h2 : ‖star U.det * U.det‖ = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, HornW.unit_star_mul hU, Matrix.det_one, norm_one]
    rw [norm_mul, norm_star] at h2
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [norm_nonneg U.det]
  rw [Matrix.det_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), Matrix.det_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), norm_mul, norm_mul, HornW.norm_det_conj_exp hWx,
    HornW.norm_det_conj_exp hWy, HornW.norm_det_conj_exp hWz, hUd, one_mul, ← Real.exp_add] at hd
  rw [Finset.sum_add_distrib]
  exact (Real.exp_injective hd).symm

end PI.ET
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ProdLeOfInjective
open Matrix Finset

noncomputable section

namespace PI.ET

theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

theorem sum_comp_perm {M : Type*} [AddCommMonoid M] {k n : ℕ} (F : (Fin k → Fin n) → M)
    (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → Fin n, F (fun i => f (τ i)) = ∑ f, F f := (Equiv.arrowCongr τ.symm (Equiv.refl (Fin n))).sum_comp F

theorem factorial_mul_det (k n : ℕ) (q : Fin n → ℂ) (V : Matrix (Fin n) (Fin k) ℂ) :
    (k.factorial : ℂ) * (Vᴴ * diagonal q * V).det =
      ∑ f : Fin k → Fin n, (∏ i, q (f i)) *
        ((V.submatrix f id).det * star (V.submatrix f id).det) := by
  have h2 : ∀ f : Fin k → Fin n, ((Vᴴ * diagonal q).submatrix id f).det =
      (∏ i, q (f i)) * star (V.submatrix f id).det := by
    intro f
    have he : (Vᴴ * diagonal q).submatrix id f = (V.submatrix f id)ᴴ * diagonal (fun i => q (f i)) := by
      ext a b
      simp [conjTranspose_apply, mul_diagonal, submatrix_apply]
    rw [he, det_mul, det_diagonal, det_conjTranspose, mul_comm]
  have h3 : ∀ (f : Fin k → Fin n) (τ : Equiv.Perm (Fin k)),
      (V.submatrix (fun i => f (τ i)) id).det = Equiv.Perm.sign τ * (V.submatrix f id).det := by
    intro f τ
    exact det_permute τ (V.submatrix f id)
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      ∑ f : Fin k → Fin n, (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
        ∑ f : Fin k → Fin n, ((Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i) *
          ((∏ i, q (f i)) * star (V.submatrix f id).det) := by
    intro τ
    rw [← sum_comp_perm (fun f : Fin k → Fin n =>
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det)) τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only
    rw [h3 f τ, Equiv.prod_comp τ (fun i => q (f i)), star_mul', star_intCast]
    ring
  rw [det_mul_rect]
  simp_rw [h2]
  rw [show (k.factorial : ℂ) * ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
      ∑ τ : Equiv.Perm (Fin k), ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]]
  rw [Finset.sum_congr rfl fun τ _ => hperm τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hd : (V.submatrix f id).det = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i := by
    rw [det_apply']
    rfl
  rw [← Finset.sum_mul, ← hd]
  ring

theorem prod_le_of_injective {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∏ i, p (f i) ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  classical
  have hs : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  set e := (Finset.univ.image f).orderEmbOfFin hs with he
  have h1 : ∏ i, p (f i) = ∏ j : Fin k, p (e j) := by
    rw [← Finset.prod_image (fun i _ j _ h => hf h), ← Finset.map_orderEmbOfFin_univ _ hs,
      Finset.prod_map]
    rfl
  have h3 : ∀ m (hm : m < k), m ≤ (e ⟨m, hm⟩ : ℕ) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hlt : e ⟨m, by omega⟩ < e ⟨m + 1, hm⟩ := e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self m))
      have h' : (e ⟨m, by omega⟩ : ℕ) < e ⟨m + 1, hm⟩ := hlt
      have := ih (by omega)
      omega
  rw [h1]
  refine Finset.prod_le_prod₀ (fun j _ => hpos _) fun j _ => hp ?_
  rw [Fin.le_iff_val_le_val, Fin.val_castLE]
  exact h3 j.1 j.2

theorem kyFan_diag {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 < p i) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  have hT := factorial_mul_det k n (fun i => (p i : ℂ)) V
  have hU := factorial_mul_det k n (fun _ => (1 : ℂ)) V
  rw [diagonal_one, Matrix.mul_one, hV, det_one, mul_one] at hU
  simp only [Finset.prod_const_one, one_mul] at hU
  have hsq : ∀ f : Fin k → Fin n, (V.submatrix f id).det * star (V.submatrix f id).det =
      ((‖(V.submatrix f id).det‖ ^ 2 : ℝ) : ℂ) := by
    intro f
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp_rw [hsq] at hU
  have hU' : (k.factorial : ℝ) = ∑ f : Fin k → Fin n, ‖(V.submatrix f id).det‖ ^ 2 := by
    exact_mod_cast hU
  set P := ∏ i : Fin k, p (Fin.castLE hk i)
  have hterm : ∀ f : Fin k → Fin n,
      ‖(∏ i, ((p (f i) : ℝ) : ℂ)) * ((V.submatrix f id).det * star (V.submatrix f id).det)‖ ≤
        P * ‖(V.submatrix f id).det‖ ^ 2 := by
    intro f
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
    by_cases hf : Function.Injective f
    · exact mul_le_mul_of_nonneg_right (prod_le_of_injective hk p hp (fun i => (hpos i).le) f hf)
        (sq_nonneg _)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        exact hf fun i j h => by_contra fun hne => hc ⟨i, j, h, hne⟩
      have h0 : (V.submatrix f id).det = 0 := det_zero_of_row_eq hne (by ext c; simp [hij])
      simp [h0]
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmain : (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ P * k.factorial := by
    calc (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖
        = ‖(k.factorial : ℂ) * (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ f : Fin k → Fin n, (∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := by rw [hT]
      _ ≤ ∑ f : Fin k → Fin n, ‖(∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin k → Fin n, P * ‖(V.submatrix f id).det‖ ^ 2 := Finset.sum_le_sum fun f _ => hterm f
      _ = P * k.factorial := by rw [← Finset.mul_sum, hU']
  nlinarith [norm_nonneg (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det]

theorem kyFanDet : KyFanDet := by
  intro n k hk p W V hp hpos hW hV
  have hW1 : Wᴴ * W = 1 := by
    have := (mem_unitaryGroup_iff').1 hW
    rwa [star_eq_conjTranspose] at this
  have hW2 : W * Wᴴ = 1 := by
    have := (mem_unitaryGroup_iff).1 hW
    rwa [star_eq_conjTranspose] at this
  have e1 : Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V =
      (Wᴴ * V)ᴴ * diagonal (fun i => (p i : ℂ)) * (Wᴴ * V) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (Wᴴ * V)ᴴ * (Wᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W,
      hW2, Matrix.one_mul, hV]
  rw [e1]
  exact kyFan_diag hk p hp hpos (Wᴴ * V) e2

end PI.ET
end
end

theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SymDist
theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
end

open MeasureTheory Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Fold

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

theorem fold_L2_first : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ := poincareSeries_finite G μ
theorem fold_L2_second : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ := fold_l2_bound_b G μ

end Fold

theorem SchurConv_holds : Formalism.L2.SG.ProjRows.SchurConv := schur_orthogonality_idempotent
theorem ConvProj_holds : Formalism.L2.SG.ProjRows.ConvProj := convolution_projection
theorem ProdConv_holds : Formalism.L2.SG.ProjRows.ProdConv := isConvIdempotent_pi
theorem RegUnitary_holds : Formalism.L2.SG.ProjRows.RegUnitary := Formalism.L2.SG.Pf.regular_representation_unitary
theorem ProjRowsR_holds : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of SchurConv_holds ConvProj_holds ProdConv_holds RegUnitary_holds

theorem GfUnimod_holds : Formalism.L2.SG.Pf.GfUnimod := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem UnimodGf_holds : Formalism.L2.SG.Pf.UnimodGf := GfUnimod_holds

theorem AutKCompact_holds : Formalism.L2.SG.Pf.AutKCompact := PI.WAU.maximal_compact_isCompact

theorem RowsBij_holds : Formalism.L2.SG.RowsDef.RowsBij :=
  Formalism.L2.SG.Pf.rows_bijective ProjRowsR_holds UnimodGf_holds

theorem level_subgroup_is_group {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.LevelSubgroupCharacter :=
  Formalism.L2.SG.Pf.level_subgroup_character_unitary X

theorem level_subgroup_properties {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.LevelSubgroupNormalized :=
  Formalism.L2.SG.Pf.levelSubgroupNormalized_of_compact X AutKCompact_holds

section Count

def latSubEquiv (I : AutInst) (x : I.GA) : PI.LatCountG.Sub I x ≃ Formalism.L2.SG.LitS.Size.Sub I x where
  toFun s := ⟨s.j, s.j_pos, s.b, s.b_ind, s.B, s.B_lat, s.b_mem, s.B_span⟩
  invFun s := ⟨s.j, s.j_pos, s.b, s.b_ind, s.B, s.B_lat, s.b_mem, s.B_span⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lattice_tau_eq_size_tau (I : AutInst) : PI.LatCountG.tau1 I = Formalism.L2.SG.LitS.Size.tau1 I := by
  funext x
  unfold PI.LatCountG.tau1 Formalism.L2.SG.LitS.Size.tau1
  congr 1
  exact Equiv.iInf_congr (latSubEquiv I x) (fun _ => rfl)

theorem LatCount_holds (I : AutInst) : Formalism.L2.SG.Count.LatCount I := by
  have h := lattice_count_all I
  unfold PI.LatCountG.LatCount at h
  unfold Formalism.L2.SG.Count.LatCount
  rw [lattice_tau_eq_size_tau] at h
  exact h

theorem DistTri_holds : Formalism.MainNotions.LeviCoordinates.DistTri := symDist_of exp_triangle_inequality

end Count

end Formalism.L2.SG.Closed
