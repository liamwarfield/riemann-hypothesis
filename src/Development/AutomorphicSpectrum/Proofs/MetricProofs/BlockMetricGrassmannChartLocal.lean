module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro h
  have hi' := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hm : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      constructor <;> simp
    simp [h] at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      show 0 < (i : ℕ) + 1 - j
      omega
    simp [h] at hm

theorem val_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨R.1, R.2.2.1⟩
  | insert a s ha ih =>
    have ih' := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h := R.2.2.2.2 (f a) _ (hf a (Finset.mem_insert_self _ _)) ih'.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h.2.1, h.2.2.2.trans (by rw [ih'.2])⟩

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ),
    M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) →
    ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧
      (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧
      ∀ m : ι k₀, z ⟨k₀, m⟩ =
        a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hblk hx hz horb
  obtain ⟨F, hFe⟩ : ∃ F, F = BM.F l := ⟨_, rfl⟩
  rw [← hFe]
  have hF : M.IsFrame F := hFe ▸ BM.isFrame l
  have hG₀ : M.GoodAt F (mCoordIdeal (BM.Rb.lift x₀ x₀)) := hFe ▸ BM.good l x₀ hx
  obtain ⟨hp1, -, hp3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨zb, hzbe⟩ : ∃ zb, zb = basePart M.blk z := ⟨_, rfl⟩
  rw [← hzbe] at horb ⊢
  have hzbm : zb ∈ mcPts (mCoordIdeal M.x) := hzbe ▸ hp1 z hz
  obtain ⟨c₀, hc₀, hc₀e⟩ := horb
  have hG : M.GoodAt F (mCoordIdeal zb) := by
    have e : mCoordIdeal zb = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
      rw [hc₀e]
      exact (GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x (BM.Rb.lift x₀ x₀) c₀ hc₀).1
    rw [e]
    exact hG₀
  have hne : ∀ k : NonPluckerBlocks M.blk, zb ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap zb (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then (zb ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩)⁻¹ else 1
  have hck : ∀ k : NonPluckerBlocks M.blk, c k.1 = (zb ⟨k, F.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hck ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · have : c k = 1 := dif_neg h
      rw [this]
      exact one_ne_zero
  have hck₀ : c k₀ = 1 := dif_neg fun h => h p hblk
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z c hc).2 hz).1
  let cb : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hb₁ : basePart M.blk z₁ = fun q => cb q.1 * zb q := by
    rw [hzbe]
    rfl
  obtain ⟨hT1, hT2⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x zb cb fun k => hc k.1
  obtain ⟨-, hval⟩ := hT2 hzbm
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hb₁, hT1]
    exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := fun k => by
    rw [hb₁]
    show c k.1 * zb ⟨k, F.c k⟩ = 1
    rw [hck, inv_mul_cancel₀ (hne k)]
  obtain ⟨hh, -, hτ, hstep⟩ := (hp3 F hF z₁ (hp1 z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨a, ha, hza⟩ := hstep p k₀ hblk
  have hvals : ∀ s, valAt M.x s (basePart M.blk z₁) = valAt M.x s zb := fun s => by
    rw [hb₁]
    exact hval s
  have hzk : ∀ m : ι k₀, z ⟨k₀, m⟩ =
      a * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) zb * minorIJ (hh p.1) I (stepCols N j p.2) := fun m => by
    have e : z₁ ⟨k₀, m⟩ = z ⟨k₀, m⟩ := by
      show c k₀ * _ = _
      rw [hck₀, one_mul]
    have := hza m
    rw [e] at this
    simpa only [hvals] using this
  refine ⟨hh p.1, a, (hτ p.1).1, (hτ p.1).2, ha, fun I hI => ?_, hzk⟩
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M.x zb hzbm
  have hδ : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := (val_sum hzbm Finset.univ (fun m : ι k₀ => F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') fun m _ =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).1).2
    rw [hF.2.2.1 p k₀ hblk I I' hI hI'] at h1
    have h2 : ∀ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') zb =
        valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb := fun m =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).2.2.1
    simp only [h2] at h1
    rw [← h1]
    split_ifs
    · exact R.2.2.2.1
    · exact R.2.2.1
  have hmin : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ (hh p.1) I' (stepCols N j p.2) = 0 := fun I' hI' =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 (hh p.1) I' (hτ p.1).1 hI').resolve_right
      (stepCols_ne_empty M.j_le p.2)
  have hsum : ∑ I', (∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb) *
      minorIJ (hh p.1) I' (stepCols N j p.2) = minorIJ (hh p.1) I (stepCols N j p.2) := by
    rw [Finset.sum_eq_single I]
    · rw [hδ I hI, if_pos rfl, one_mul]
    · intro I' _ hne'
      by_cases hs : IsStepRows N j p.2 I'
      · rw [hδ I' hs, if_neg (Ne.symm hne'), zero_mul]
      · rw [hmin I' hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  have hplk : plk M F k₀ z I = ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * z ⟨k₀, m⟩ := by
    rw [hzbe]
    rfl
  rw [hplk, ← hsum, Finset.mul_sum]
  simp only [hzk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocalStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_grassmann_chart_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧ (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧ ∀ m : ι k₀, z ⟨k₀, m⟩ = a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mixWord {n : ℕ} (a a₀ A' : HermLine ι) (k i : ℕ) : Fin n → HermLine ι :=
  fun j => if (j : ℕ) < i then a else if (j : ℕ) + 1 < k then a₀ else A'


open Classical in
def logRatio (a a₀ : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (a₀.h z) - Real.log (a.h z) else 0

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmetic
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlArith
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_fl_arith : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
  intro Ψ _ _ _ N hN
  have h := FlagArithVar.proof Ψ N hN
  rwa [dimFl, ← Nat.choose_two_right] at h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmetic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pFl_isArithVar : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) :=
  @PositivityTheory.Xgp.t_c_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmeticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_arithmetic : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar | exact GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunction
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunction
set_option maxSynthPendingDepth 1
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem cuspWeight_descends :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
      [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
      [Module O Lt] (X : ComponentSetting D O Lt),
      ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧
        (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, C', hC⟩ := CuspWeightIntegrable.uFn_bound X
  letI : MeasurableSpace X.M.Xc := borel X.M.Xc
  haveI : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ⟨fun x => 2 * CuspWeightIntegrable.uFn X x, 2 * max C C', ?_, ?_, ?_⟩
  · exact ((CuspWeightIntegrable.measurable_uFn X).const_mul 2).indicator X.S.R.isOpen_Yo.measurableSet
  · intro x hx
    have h1 := hC x hx
    have hl := Real.log_nonneg (X.S.R.one_le_r x hx)
    have h2 : C' * Real.log (X.S.R.r x) ≤ max C C' * Real.log (X.S.R.r x) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hl
    have h3 : C ≤ max C C' := le_max_left _ _
    rw [abs_mul, abs_two]
    nlinarith
  · intro z hz hy
    have hzB : z ∉ D.Bd := by
      intro hB
      obtain ⟨z0, ⟨hz0X, hz0m⟩, hp⟩ := X.S.Yo_sub _ hy
      obtain ⟨c, hc, rfl⟩ := (X.M.fibre z hz z0 hz0m).1 hp.symm
      exact hz0X.2 (D.bd_torus z hB c hc)
    have := CuspWeightIntegrable.cuspWeight_eq X hz hzB hy
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunctionStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspWeight_factors_through_measurable_log_bounded : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt), ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧ (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | exact GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.cuspWeight_descends <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChoose
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChoose
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept

variable {Ψ : Type} {N j : ℕ}

theorem stepOf_val' (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem' (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top' (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper' (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val' N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

theorem sep_of_all (hj : j ≤ N) {keep : Ψ × Fin N → Prop} (hk : ∀ p, keep p) (q : LowIdx Ψ N j) : Sep keep q :=
  ⟨stepOf N j q.1.2.2, hk _, stepOf_proper' hj q.2.1 q.2.2, stepOf_mem' hj _,
    fun h => absurd (stepOf_top' hj _ _ h) (not_le.2 q.2.1)⟩

theorem card_pIdx_of_all : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N →
    (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro Ψ _ _ N j keep hj hk
  have e : PIdx j keep ≃ LowIdx Ψ N j := Equiv.subtypeUnivEquiv (sep_of_all hj hk)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChooseStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_pIdx_eq_choose : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N → (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegular
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Flag

variable {Ψ : Type} {N j n e : ℕ}

theorem analytic_pMat (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ PIdx j keep ≃ Fin e)
    (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pMat keep (pL ε w) τ a b) s := by
  unfold pMat lowMat
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · simp only [hc, dite_true]
    by_cases hs : Sep keep (⟨(τ, a, b), hc⟩ : LowIdx Ψ N j)
    · simp only [cExt, hs, dite_true, pL]
      exact analytic_coord _
    · simp only [cExt, hs, dite_false]
      exact analyticOnNhd_const
  · simp only [hc, dite_false]
    exact analyticOnNhd_const

theorem analytic_pH (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pH keep h ε τ w a b) s := by
  unfold pH
  exact analytic_mul_entry (fun _ => h τ) _ (fun _ _ => analyticOnNhd_const)
    (analytic_pMat keep s ε τ) a b

theorem analytic_pB {Λ : Type} (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (pB ε) (pD ε V) := by
  have : pB ε = ⇑(ContinuousLinearMap.pi (R := ℂ) fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (ε (Sum.inl i))) := by
    funext w i
    rfl
  rw [this]
  exact fun w _ => ContinuousLinearMap.analyticAt _ w

end Flag

theorem pPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc p
  obtain ⟨-, -, -, hb, -⟩ := hc
  obtain ⟨-, -, hbl, hval, -⟩ := hb
  have hmap : Set.MapsTo (pB ε) (pD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (pB ε w) q) (pD ε V) := fun q =>
    (hbl q).comp (analytic_pB ε V) hmap
  have hv : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (pB ε w))) (pD ε V) := fun q I =>
    (hval q I).comp (analytic_pB ε V) hmap
  exact analytic_flagZ M F (fun w => bl (pB ε w)) (fun w τ' => pH keep h ε τ' w) hzb hv
    (fun τ' => analytic_pH keep _ h ε τ') (v p)

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegularStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_resolution_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisation
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticLiftToLogResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib


open GlobalTheory.CompanionTheory.Ar.PB.Proj in
theorem holo_of_lift_orbit_top :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D) (V : Set (Fin e → ℂ)) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (h : (Fin e → ℂ) → R.X), J = ⊤ → IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, SameOrbit (R.lift (h u) (h u)) (zex u)) → ContinuousOn h V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ h) (V ∩ h ⁻¹' (R.A.chart k).source) := by
  open GlobalTheory.CompanionTheory.Ar.PB.Proj in
  intro K _ ι _ P J D e R V zex h hJ hV han hmc horb
  subst hJ
  have hloc : ∀ x, ∀ u ∈ V, h u ∈ R.U x → SameOrbit (R.lift x (h u)) (zex u) := fun x u hu hx =>
    orbit_trans (R.compat x (h u) (h u) ⟨hx, R.mem_U (h u)⟩) (horb u hu)
  have hcont : ∀ u0 ∈ V, ContinuousAt h u0 := by
    intro u0 hu0
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro x _ hx
    obtain ⟨𝒰, h𝒰, hx𝒰⟩ := mapClusterPt_iff_ultrafilter.1 hx
    have hev : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V ∧ h u ∈ R.U x := by
      have e1 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V := h𝒰 (hV.mem_nhds hu0)
      have e2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), h u ∈ R.U x :=
        hx𝒰 ((R.isOpen_U x).mem_nhds (R.mem_U x))
      exact e1.and e2
    have hlim : ∀ q, Filter.Tendsto (fun u => R.lift x (h u) q) 𝒰 (𝓝 (R.lift x x q)) := fun q =>
      (continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hx𝒰
    have hzlim : ∀ q, Filter.Tendsto (fun u => zex u q) 𝒰 (𝓝 (zex u0 q)) := fun q =>
      (han q u0 hu0).continuousAt.tendsto.comp (Filter.tendsto_id'.2 h𝒰)
    have horb0 : SameOrbit (R.lift x x) (zex u0) := by
      refine orbit_of_cross (R.mem x x (R.mem_U x)).1 (hmc u0 hu0).1 ?_
      intro k i i'
      have h1 := ((hlim ⟨k, i⟩).mul (hzlim ⟨k, i'⟩)).sub ((hlim ⟨k, i'⟩).mul (hzlim ⟨k, i⟩))
      have h2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)),
          (0 : ℂ) = R.lift x (h u) ⟨k, i⟩ * zex u ⟨k, i'⟩ - R.lift x (h u) ⟨k, i'⟩ * zex u ⟨k, i⟩ :=
        hev.mono fun u hu => (sub_eq_zero.2 (orbit_cross (hloc x u hu.1 hu.2) k i i')).symm
      have h3 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2)
      exact sub_eq_zero.1 h3
    exact R.inj x (h u0) (not_mem_mcPts_top _) (orbit_trans horb0 (orbit_symm (horb u0 hu0)))
  refine ⟨fun u hu => (hcont u hu).continuousWithinAt, ?_⟩
  rintro k u0 ⟨hu0, hs0⟩
  have hs0' : h u0 ∈ (R.A.chart k).source := hs0
  choose p hp using (R.mem (h u0) (h u0) (R.mem_U (h u0))).1
  have hsym : (R.A.chart k).symm (R.A.chart k (h u0)) = h u0 := (R.A.chart k).left_inv hs0'
  have ha : AnalyticAt ℂ (fun w => affCoord p (R.lift (h u0) ((R.A.chart k).symm w))) (R.A.chart k (h u0)) :=
    analyticAt_affCoord R.A (R.holo (h u0)) k ((R.A.chart k).map_source hs0')
      (by rw [hsym]; exact R.mem_U (h u0)) p (by rw [hsym]; exact hp)
  have hker := R.immersion (h u0) (not_mem_mcPts_top _) p hp k hs0'
  obtain ⟨G, hG, hGa⟩ := exists_analytic_retraction ha hker
  have hzp : ∀ k', zex u0 ⟨k', p k'⟩ ≠ 0 := fun k' => orbit_ne (horb u0 hu0) (hp k')
  have hb : AnalyticAt ℂ (fun u => affCoord p (zex u)) u0 := by
    rw [analyticAt_pi_iff]
    intro q
    exact (han q u0 hu0).div (han ⟨q.1, p q.1⟩ u0 hu0) (hzp q.1)
  have hG' : AnalyticAt ℂ G (affCoord p (zex u0)) := by
    have hab : affCoord p (R.lift (h u0) ((R.A.chart k).symm (R.A.chart k (h u0)))) = affCoord p (zex u0) := by
      rw [hsym]; exact affCoord_eq (horb u0 hu0) p
    rw [← hab]; exact hG
  refine (AnalyticAt.comp (g := G) (f := fun u => affCoord p (zex u)) hG' hb).congr ?_
  filter_upwards [hV.mem_nhds hu0,
    (hcont u0 hu0).eventually (((R.isOpen_U (h u0)).inter (R.A.chart k).open_source).mem_nhds ⟨R.mem_U (h u0), hs0'⟩),
    (((R.A.chart k).continuousAt hs0').tendsto.comp (hcont u0 hu0)).eventually hGa] with u hu hhu hGu
  simp only [Function.comp_apply] at hGu ⊢
  rw [← hGu, (R.A.chart k).left_inv hhu.2, affCoord_eq (hloc (h u0) u hu hhu.1) p]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisation
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holoOn {D e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) {V : Set (Fin e → ℂ)}
    {Y : Set X} {g : X → ℂ} (hg : A.HoloOn Y g) {h : (Fin e → ℂ) → X} {z : Fin e → ℂ}
    (hV : V ∈ 𝓝 z) (hc : ContinuousOn h V)
    (ha : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ h) (V ∩ h ⁻¹' (A.chart k).source)) (hz : h z ∈ Y) :
    AnalyticAt ℂ (g ∘ h) z := by
  obtain ⟨k, hk⟩ := A.cover (h z)
  have hcz : ContinuousAt h z := hc.continuousAt hV
  have h1 : AnalyticAt ℂ (A.chart k ∘ h) z := ha k z ⟨mem_of_mem_nhds hV, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h) z) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simpa [Set.mem_preimage, (A.chart k).left_inv hk] using hz
  have h3 : AnalyticAt ℂ ((g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h)) z := h2.comp h1
  refine h3.congr ?_
  filter_upwards [hcz.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  simp [(A.chart k).left_inv hu]

theorem ref_pot_along_exact_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  intro K _ ι _ D σ S P Re a e V ΦY zex z hJ hdeg hbr hV hzV hana hmc hex
  have hbij : Function.Bijective Re.π := realis_bijective_of_degree_one K ι D σ S P Re hdeg hbr
  set h : (Fin e → ℂ) → Re.R.X := fun u => Function.surjInv hbij.2 (ΦY u) with hdef
  have hπ : ∀ u, Re.π (h u) = ΦY u := fun u => Function.surjInv_eq hbij.2 (ΦY u)
  have hSO : ∀ u ∈ V, SameOrbit (Re.R.lift (h u) (h u)) (zex u) := fun u hu => hex u hu (h u) (hπ u)
  obtain ⟨hc, hch⟩ := holo_of_lift_orbit_top K ι P Re.J D e Re.R V zex h hJ hV hana hmc hSO
  have hVn : V ∈ 𝓝 z := hV.mem_nhds hzV
  have hcz : ContinuousAt h z := hc.continuousAt hVn
  obtain ⟨W, hW, hxW, G, hG, hGeq⟩ := Re.ref_pot a (h z) (Set.mem_univ _)
  have hGh : AnalyticAt ℂ (G ∘ h) z := analyticAt_comp_of_holoOn Re.R.A hG hVn hc hch hxW
  have hxU : h z ∈ Re.R.U (h z) := Re.R.mem_U _

  have hi : ∀ k, ∃ i, zex z ⟨k, i⟩ ≠ 0 := (hmc z hzV).1
  choose i hi using hi
  set c : K → (Fin e → ℂ) → ℂ := fun k u => Re.R.lift (h z) (h u) ⟨k, i k⟩ / zex u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) z := fun k =>
    AnalyticAt.div (analyticAt_comp_of_holoOn Re.R.A (Re.R.holo (h z) ⟨k, i k⟩) hVn hc hch hxU)
      (hana _ z hzV) (hi k)
  have hcz0 : ∀ k, c k z ≠ 0 := by
    intro k
    obtain ⟨d, hd, hdz⟩ := hSO z hzV
    have : Re.R.lift (h z) (h z) ⟨k, i k⟩ = d k * zex z ⟨k, i k⟩ := congrFun hdz ⟨k, i k⟩
    simp only [hcdef, this]
    exact div_ne_zero (mul_ne_zero (hd k) (hi k)) (hi k)
  have hL : ∀ k, ∃ Lk : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Lk z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖c k z'‖ = (Lk z').re :=
    fun k => log_norm_eventually_eq_re_analyticAt e (c k) z (hcan k) (hcz0 k)
  choose L hLan hLeq using hL
  refine ⟨fun u => (∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u), ?_, ?_⟩
  · refine AnalyticAt.sub ?_ hGh
    exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (hLan k)
  · have hne : ∀ᶠ u in 𝓝 z, ∀ k, zex u ⟨k, i k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hana _ z hzV).continuousAt.eventually_ne (hi k)
    filter_upwards [hVn, hne, eventually_all.2 hLeq, hcz.preimage_mem_nhds (hW.mem_nhds hxW),
      hcz.preimage_mem_nhds ((Re.R.isOpen_U (h z)).mem_nhds hxU)] with u huV hune huL huW huU
    have hcompat := Re.R.compat (h z) (h u) (h u) ⟨huU, Re.R.mem_U _⟩
    obtain ⟨d₁, hd₁, e₁⟩ := hcompat
    obtain ⟨d₂, hd₂, e₂⟩ := hSO u huV
    have hlift : Re.R.lift (h z) (h u) = fun p => (d₁ p.1 * d₂ p.1) * zex u p := by
      funext p
      rw [congrFun e₁ p, congrFun e₂ p, mul_assoc]
    have hck : ∀ k, c k u = d₁ k * d₂ k := by
      intro k
      simp only [hcdef, hlift]
      field_simp [hune k]
    have hlift' : Re.R.lift (h z) (h u) = fun p => c p.1 u * zex u p := by
      rw [hlift]; funext p; rw [hck]
    have hcne : ∀ k, c k u ≠ 0 := fun k => by
      rw [hck]; exact mul_ne_zero (hd₁ k) (hd₂ k)
    have hsm := (Re.ref a).smul (fun k => c k u) (zex u) hcne
    have hpos := (Re.ref a).pos (zex u) (hmc u huV).1
    have hlog : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) + Real.log ((Re.ref a).h (zex u)) := by
      rw [hlift', hsm, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))) hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))
    have hG' : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) - (S.th a).φ (ΦY z) (ΦY u) = (G (h u)).re := by
      have := hGeq (h u) huW
      simpa only [potOf, LocPot.pullback, hπ] using this
    have hre : ((∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u)).re =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) - (G (h u)).re := by
      rw [Complex.sub_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [huL k]
      simp
    rw [hre]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_lift_realisation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorization
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.BigCellLU

variable {N : ℕ}

abbrev square_block_restriction (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) : Matrix {x // x ∈ T} {x // x ∈ T} ℂ :=
  G.submatrix Subtype.val Subtype.val

theorem minorIJ_self (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) :
    minorIJ G T T = (square_block_restriction G T).det := by
  unfold minorIJ
  rw [dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self (T.orderIsoOfFin rfl).toEquiv (square_block_restriction G T)]
  congr 1

theorem det_squareBlockRestriction_ne_zero (G : Matrix (Fin N) (Fin N) ℂ) (hd : G.det ≠ 0) (T : Finset (Fin N))
    (h : ∀ x ∈ T, ∀ c, c ∉ T → G⁻¹ x c = 0) : (square_block_restriction G T).det ≠ 0 := by
  have hB : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hd)
  have hprod : square_block_restriction G⁻¹ T * square_block_restriction G T = 1 := by
    ext x y
    have h1 : (G⁻¹ * G) x.1 y.1 = (1 : Matrix (Fin N) (Fin N) ℂ) x.1 y.1 := by rw [hB]
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ T)
      (f := fun c => G⁻¹ x.1 c * G c y.1) (fun c _ hc => by rw [h x.1 x.2 c hc, zero_mul]),
      ← Finset.sum_coe_sort T, Matrix.one_apply] at h1
    have h3 : (square_block_restriction G⁻¹ T * square_block_restriction G T) x y = ∑ i : {x // x ∈ T}, G⁻¹ x.1 i.1 * G i.1 y.1 := rfl
    rw [h3, h1, Matrix.one_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos (congrArg Subtype.val hxy)]
    · rw [if_neg hxy, if_neg (fun h => hxy (Subtype.ext h))]
  intro h0
  have h2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h2
  exact zero_ne_one h2

theorem exists_cols (G : Matrix (Fin N) (Fin N) ℂ) (F : Set (Finset (Fin N))) (hcov : ∀ b, ∃ T ∈ F, b ∈ T)
    (hnest : ∀ T ∈ F, ∀ T' ∈ F, ∀ b, b ∈ T → b ∈ T' → T ⊆ T' ∨ T' ⊆ T)
    (hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0) :
    ∃ W : Matrix (Fin N) (Fin N) ℂ, (∀ T ∈ F, ∀ c ∈ T, ∀ x, x ∉ T → W x c = 0) ∧
      ∀ a b, (∀ T ∈ F, b ∈ T → a ∈ T) → (G * W) a b = if a = b then 1 else 0 := by
  have hex : ∀ b, ∃ n, ∃ T ∈ F, b ∈ T ∧ T.card = n := fun b => by
    obtain ⟨T, hT, hb⟩ := hcov b
    exact ⟨T.card, T, hT, hb, rfl⟩
  have hmin : ∀ b, ∃ T ∈ F, b ∈ T ∧ ∀ T' ∈ F, b ∈ T' → T ⊆ T' := by
    intro b
    obtain ⟨T, hTF, hbT, hcard⟩ := Nat.find_spec (hex b)
    refine ⟨T, hTF, hbT, fun T' hT'F hbT' => ?_⟩
    rcases hnest T hTF T' hT'F b hbT hbT' with h1 | h1
    · exact h1
    · have hle : T.card ≤ T'.card := by
        rw [hcard]
        exact Nat.find_min' (hex b) ⟨T', hT'F, hbT', rfl⟩
      exact le_of_eq (Finset.eq_of_subset_of_card_le h1 hle).symm
  choose Tb hTbF hbTb hTbmin using hmin
  refine ⟨Matrix.of fun x b => if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0, ?_, ?_⟩
  · intro T hT c hc x hx
    have hx' : x ∉ Tb c := fun h' => hx (hTbmin c T hT hc h')
    simp only [Matrix.of_apply, dif_neg hx']
  · intro a b hab
    have ha : a ∈ Tb b := hab (Tb b) (hTbF b) (hbTb b)
    have hM : square_block_restriction G (Tb b) * (square_block_restriction G (Tb b))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv _ (hTbF b)))
    have h1 := congrFun (congrFun hM ⟨a, ha⟩) ⟨b, hbTb b⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have h2 : ∀ x : {x // x ∈ Tb b}, G a x.1 * (if hx : x.1 ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x.1, hx⟩ ⟨b, hbTb b⟩ else 0) =
        square_block_restriction G (Tb b) ⟨a, ha⟩ x * (square_block_restriction G (Tb b))⁻¹ x ⟨b, hbTb b⟩ := by
      intro x
      rw [dite_eq_left x.2]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Tb b))
      (f := fun x => G a x * (if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0))
      (fun x _ hx => by simp only [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort (Tb b), Finset.sum_congr rfl (fun x _ => h2 x), h1]
    simp only [Subtype.mk.injEq]

def IsSeg (N j : ℕ) (T : Finset (Fin N)) : Prop :=
  (∃ m, m ≤ N - j ∧ T = Finset.univ.filter fun a : Fin N => (a : ℕ) < m) ∨
    ∃ m, T = Finset.univ.filter fun a : Fin N => N - j ≤ (a : ℕ) ∧ (a : ℕ) < m

theorem isSeg_omIdx (N j : ℕ) : IsSeg N j (omIdx N j) := by
  exact Or.inl ⟨N - j, le_refl _, rfl⟩

theorem isSeg_wIdx (N j : ℕ) : IsSeg N j (wIdx N j) :=
  Or.inr ⟨N, by ext a; simp [wIdx]⟩

theorem isSeg_stepCols (N j : ℕ) (i : Fin N) : IsSeg N j (stepCols N j i) := by
  have hi := i.isLt
  unfold IsSeg stepCols
  by_cases h : (i : ℕ) + 1 ≤ j
  · right
    exact ⟨N - j + ((i : ℕ) + 1), by ext a; simp [h]⟩
  · left
    exact ⟨(i : ℕ) + 1 - j, by omega, by ext a; simp [h]⟩

theorem IsSeg.nested {N j : ℕ} {T T' : Finset (Fin N)} (h : IsSeg N j T) (h' : IsSeg N j T') {b : Fin N}
    (hb : b ∈ T) (hb' : b ∈ T') : T ⊆ T' ∨ T' ⊆ T := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;> rcases h' with ⟨m', hm', rfl⟩ | ⟨m', rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
  all_goals first
    | (exfalso; omega)
    | (rcases le_total m m' with hmm | hmm
       · left
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega
       · right
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega)

theorem IsSeg.down {N j : ℕ} {T : Finset (Fin N)} (h : IsSeg N j T) {a b : Fin N} (hb : b ∈ T) (hab : a < b)
    (hs : (a : ℕ) < N - j ↔ (b : ℕ) < N - j) : a ∈ T := by
  have hab' : (a : ℕ) < b := hab
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  · omega
  · have h1 : ¬ ((b : ℕ) < N - j) := by omega
    have h2 : ¬ ((a : ℕ) < N - j) := fun h => h1 (hs.mp h)
    omega

theorem exists_lu : ∀ (N j : ℕ) (kp : Fin N → Prop) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i, kp i → IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L W : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ (∀ a b : Fin N, b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → (¬ ∃ i, kp i ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L a b = 0) ∧ IsBlockDiag j W ∧ (∀ i, kp i → IsProperStep N j i → ∀ c ∈ stepCols N j i, ∀ x, x ∉ stepCols N j i → W x c = 0) ∧ G * W = L := by
  intro N j kp G hjN hbd hdet hstep
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have hGinv : ∀ x c : Fin N, ¬ ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) → G⁻¹ x c = 0 := by
    set E : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of (fun x c => if ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) then G⁻¹ x c else 0) with hEdef
    have hE : G * E = 1 := by
      ext a c
      by_cases hac : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
      · rw [← hGG, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [if_pos hxc]
        · rw [if_neg hxc, hbd a x (fun hax => hxc (hax.symm.trans hac)), zero_mul, zero_mul]
      · have hne : a ≠ c := fun h => hac (by rw [h])
        rw [Matrix.one_apply_ne hne, Matrix.mul_apply]
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [hbd a x (fun hax => hac (hax.trans hxc)), zero_mul]
        · rw [if_neg hxc, mul_zero]
    have hEinv : G⁻¹ = E := Matrix.inv_eq_right_inv hE
    intro x c hxc
    rw [hEinv, hEdef, Matrix.of_apply, if_neg hxc]
  have hom : (square_block_restriction G (omIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact hc (h.mp hx)))
  have hw : (square_block_restriction G (wIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact (not_lt.mpr hx) (h.mpr (not_le.mp hc))))
  let F : Set (Finset (Fin N)) := {T | (∃ i, kp i ∧ IsProperStep N j i ∧ T = stepCols N j i) ∨
    T = omIdx N j ∨ T = wIdx N j}
  have hseg : ∀ T ∈ F, IsSeg N j T := by
    rintro T (⟨i, -, -, rfl⟩ | rfl | rfl)
    · exact isSeg_stepCols N j i
    · exact isSeg_omIdx N j
    · exact isSeg_wIdx N j
  have hcov : ∀ b, ∃ T ∈ F, b ∈ T := by
    intro b
    by_cases hb : (b : ℕ) < N - j
    · exact ⟨omIdx N j, Or.inr (Or.inl rfl), by
        simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩
    · exact ⟨wIdx N j, Or.inr (Or.inr rfl), by
        simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hb⟩
  have hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0 := by
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl)
    · rw [← minorIJ_self]
      exact hstep i hki hpi
    · exact hom
    · exact hw
  obtain ⟨W, hWsupp, hGW⟩ := exists_cols G F hcov
    (fun T hT T' hT' b hb hb' => (hseg T hT).nested (hseg T' hT') hb hb') hinv
  have hWblk : IsBlockDiag j W := by
    intro x c hxc
    by_cases hc : (c : ℕ) < N - j
    · refine hWsupp (omIdx N j) (Or.inr (Or.inl rfl)) c ?_ x ?_
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_true hx hc)
    · refine hWsupp (wIdx N j) (Or.inr (Or.inr rfl)) c ?_ x ?_
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hc
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_false (not_lt.mpr hx) hc)
  have hLblk : IsBlockDiag j (G * W) := by
    intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hxb : ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hbd a x (fun hax => hab (hax.trans hxb)), zero_mul]
    · rw [hWblk x b hxb, mul_zero]
  refine ⟨G * W, W, hLblk, ⟨fun a => ?_, fun a b hab => ?_⟩, ?_, hWblk, ?_, rfl⟩
  · rw [hGW a a (fun T _ h => h), if_pos rfl]
  · by_cases hs : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hGW a b (fun T hT hb => (hseg T hT).down hb hab hs), if_neg (ne_of_lt hab)]
    · exact hLblk a b hs
  · intro a b hba hs hno
    refine (hGW a b ?_).trans (if_neg (ne_of_gt hba))
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl) hb
    · by_contra ha
      exact hno ⟨i, hki, hpi, hb, ha⟩
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hs.mpr hb
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact not_lt.mp (fun h => (not_lt.mpr hb) (hs.mp h))
  · intro i hki hpi c hc x hx
    exact hWsupp _ (Or.inl ⟨i, hki, hpi, rfl⟩) c hc x hx

end GlobalTheory.CompanionTheory.Ar.PB.BigCellLU
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorizationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerUni_blockDiag_factorization : ∀ (N j : ℕ) (kp : Fin N → Prop) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i, kp i → IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L W : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ (∀ a b : Fin N, b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → (¬ ∃ i, kp i ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L a b = 0) ∧ IsBlockDiag j W ∧ (∀ i, kp i → IsProperStep N j i → ∀ c ∈ stepCols N j i, ∀ x, x ∉ stepCols N j i → W x c = 0) ∧ G * W = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu | exact GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BigCellLU.exists_lu <;> assumption)
end
end
