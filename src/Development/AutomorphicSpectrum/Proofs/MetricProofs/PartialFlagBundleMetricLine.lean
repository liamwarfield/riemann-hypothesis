module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPsh
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackThird
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerCell
public import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFourth

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XGramSize
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.gram_size

theorem one {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) (m : ℝ) (hm : 1 ≤ m) (hA : A.PosDef) (hB : B.PosDef)
    (h : ((m : ℂ) • B - A).PosSemidef) : Real.log A.det.re - Real.log B.det.re ≤ k * Real.log m := by
  have h1 : A.det.re ≤ ((m : ℂ) • B).det.re :=
    GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.proof k ((m : ℂ) • B) A hA.posSemidef h
  have e : ((m : ℂ) • B).det.re = m ^ k * B.det.re := by
    rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hA' : 0 < A.det.re := by simpa using (Complex.lt_def.mp hA.det_pos).1
  have hB' : 0 < B.det.re := by simpa using (Complex.lt_def.mp hB.det_pos).1
  have hm' : 0 < m := by linarith
  rw [e] at h1
  have h2 := Real.log_le_log hA' h1
  rw [Real.log_mul (by positivity) hB'.ne', Real.log_pow] at h2
  linarith

end PositivityTheory.Xgp.gram_size

theorem PositivityTheory.Xgp.t_gram_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  intro n k G G₀ V m hm hG₀ hG h1 h2 hV
  have hinj : Function.Injective V.mulVec := Matrix.mulVec_injective_iff.mpr hV
  have hA : (Vᴴ * G * V).PosDef := hG.conjTranspose_mul_mul_same hinj
  have hB : (Vᴴ * G₀ * V).PosDef := hG₀.conjTranspose_mul_mul_same hinj
  have e1 : Vᴴ * ((m : ℂ) • G₀ - G) * V = (m : ℂ) • (Vᴴ * G₀ * V) - Vᴴ * G * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : Vᴴ * ((m : ℂ) • G - G₀) * V = (m : ℂ) • (Vᴴ * G * V) - Vᴴ * G₀ * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have p1 := h1.conjTranspose_mul_mul_same V
  have p2 := h2.conjTranspose_mul_mul_same V
  rw [e1] at p1
  rw [e2] at p2
  have a1 := PositivityTheory.Xgp.gram_size.one _ _ m hm hA hB p1
  have a2 := PositivityTheory.Xgp.gram_size.one _ _ m hm hB hA p2
  rw [abs_sub_le_iff]
  constructor <;> linarith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThird
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonic
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_det_log_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m :=
  PositivityTheory.Xgp.t_gram_size

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonicStatement
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_comparable_gram_bound : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | exact GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThird
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize

theorem continuousAt_of_chart {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    (c : OpenPartialHomeomorph X E) {f : X → F} {x : X} (hx : x ∈ c.source)
    (h : ContinuousAt (f ∘ c.symm) (c x)) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x := ContinuousAt.comp h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  simp [c.left_inv hz]

theorem holoOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    {g : X → ℂ} (h : A.HoloOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact (h j _ hm).continuousAt

theorem smoothOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    (hW : IsOpen W) {g : X → ℝ} (h : A.SmoothOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  exact ((h j).continuousOn).continuousAt (ho.mem_nhds hm)

variable {N : ℕ}

theorem gram_cmp {k : ℕ} (hk : k ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (V : Matrix (Fin N) (Fin k) ℂ) {m : ℝ}
    (hm : 1 ≤ m) (hG : G.PosDef) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) (hV : LinearIndependent ℂ Vᵀ) :
    |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by
  refine (GlobalTheory.T.log_det_comparable_gram_bound N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_
  have : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg hm)

theorem card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using S.card_le_univ

theorem blockPot_sub_le (j : ℕ) (i : Fin N) {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) :
    |blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by
  obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h
  obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h
  have e1 := hP hG
  have e2 := hP1 Matrix.PosDef.one
  have tW := abs_le.1 (gram_cmp (card_le (wIdx N j)) (selM (wIdx N j)) hm hG h1 h2 (hS _))
  have tO := abs_le.1 (gram_cmp (card_le (omIdx N j)) (selM (omIdx N j)) hm hG h1 h2 (hS _))
  have tH := abs_le.1 (gram_cmp (card_le (stepCols N j i)) (h * selM (stepCols N j i)) hm hG h1 h2 (hHS hd _))
  have hl : 0 ≤ (N : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm)
  rw [e1, e2, abs_le]
  split_ifs <;> constructor <;> linarith [tW.1, tW.2, tO.1, tO.2, tH.1, tH.2]

theorem size_abs {G : Matrix (Fin N) (Fin N) ℂ} {r c : ℝ} (hr : 1 ≤ r) (hG : G.PosDef)
    (h : (((r ^ c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ c : ℝ) : ℂ) • G - 1).PosSemidef) :
    (((r ^ |c| : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ |c| : ℝ) : ℂ) • G - 1).PosSemidef := by
  have hd : (0 : ℝ) ≤ r ^ |c| - r ^ c := sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))
  have hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ) := by exact_mod_cast hd
  constructor
  · have := h.1.add (Matrix.PosSemidef.one.smul hd')
    convert this using 1
    push_cast
    module
  · have := h.2.add (hG.posSemidef.smul hd')
    convert this using 1
    push_cast
    module

theorem gram_one_pos {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * 1 * h) S S).re := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hp : (hᴴ * 1 * h).PosDef :=
    Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  exact (Complex.lt_def.1 (GramPot.minor_pos hp S)).1

theorem continuous_gram (S : Finset (Fin N)) :
    Continuous fun h : Matrix (Fin N) (Fin N) ℂ => (minorIJ (hᴴ * 1 * h) S S).re := by
  simp only [minorIJ, dif_pos]
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  fun_prop

theorem continuousAt_blockPot_one {X : Type*} [TopologicalSpace X] (j : ℕ) (i : Fin N)
    {H : X → Matrix (Fin N) (Fin N) ℂ} {x : X} (hH : ∀ a b, ContinuousAt (fun y => H y a b) x)
    (hd : (H x).det ≠ 0) : ContinuousAt (fun y => blockPot j i 1 (H y)) x := by
  have hc : ContinuousAt H x :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b
  unfold blockPot
  refine continuousAt_const.add ?_
  split_ifs
  · refine continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)
    exact (gram_one_pos hd _).ne'
  · exact continuousAt_const

theorem stepPh_le_log : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot
  have hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x := fun x => by
    have := BM.norm_le x
    simp only [rW]
    linarith
  have hrpos : ∀ x, 0 < rW BM.L BM.s x := fun x => (Real.exp_pos 1).trans_le (hr x)
  have hr1 : ∀ x, 1 ≤ rW BM.L BM.s x := fun x =>
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)
  have hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x) := fun x =>
    (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)
  have key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
    intro y₀
    obtain ⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩ := hch y₀ y₀ (R.mem_U y₀)
    let u : R.X → ℝ := fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ -
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))
    have hu : ContinuousAt u y₀ := by
      refine ((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀)
        (hHd y₀ hy₀).2).add ?_).sub ?_
      · exact ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))
      · exact smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)
    refine ⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀)
      (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩
    rintro y' ⟨hy'W, hy'u⟩ hb
    have hb' : pr y' ∉ bdry BM.s := hb
    have hmem : pr y' ∈ BM.O l \ bdry BM.s := ⟨hO y' hy'W, hb'⟩
    obtain ⟨-, hpd⟩ := BM.G_pos l p.1 _ hmem
    have hs := size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)
    have hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst| := Real.one_le_rpow (hr1 _) (abs_nonneg _)
    have hdiff := blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2
    rw [Real.log_rpow (hrpos _)] at hdiff
    have e' := heq y' hy'W hb'
    have hL := hlog (pr y')
    have hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y' := by
      simp only [u]
      linarith
    change |stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))
    rw [hsum]
    have hu' : |u y'| < |u y₀| + 1 := hy'u
    have hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) :=
      le_mul_of_one_le_right (by positivity) hL
    calc _ ≤ |blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')| + |u y'| := abs_add_le _ _
      _ ≤ (3 / 2) * N * (|BM.Cst| * Real.log (rW BM.L BM.s (pr y'))) + (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) := by
        linarith
      _ = _ := by ring
  have hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := fun x =>
    zero_le_one.trans (hlog (pr x))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := R.X)).induction_on
    (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x))
    ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx hb => hx.elim
      (fun h => (hC x h hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogr x)))
      (fun h => (hC' x h hb).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlogr x)))⟩)
    (fun y₀ _ => by
      obtain ⟨t, ht, C, hC⟩ := key y₀
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)
  exact ⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviForm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalBruhatCellAnalyticCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalBruhatCellAnalyticCoordinates
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem holomorphic_factor_big_cell :
    ∀ (e N : ℕ) (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (x₀ : Fin e → ℂ), (∀ a b, AnalyticAt ℂ (fun x => g x a b) x₀) → (g x₀).BlockTriangular id → IsUnit (g x₀).det → ∃ (z : (Fin e → ℂ) → Pairs N → ℂ) (b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), AnalyticAt ℂ z x₀ ∧ (∀ p q, AnalyticAt ℂ (fun x => b x p q) x₀) ∧ z x₀ = 0 ∧ (∀ᶠ x in 𝓝 x₀, (b x).BlockTriangular id ∧ IsUnit (b x).det ∧ g x = cellMat N (z x) * b x) ∧ ∀ v, fderiv ℂ z x₀ v = 0 ↔ ((g x₀)⁻¹ * Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v).BlockTriangular id :=
  PositivityTheory.Xgp.t_per_cell

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalBruhatCellAnalyticCoordinatesStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bruhat_cell_analytic_coordinates : ∀ (e N : ℕ) (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (x₀ : Fin e → ℂ), (∀ a b, AnalyticAt ℂ (fun x => g x a b) x₀) → (g x₀).BlockTriangular id → IsUnit (g x₀).det → ∃ (z : (Fin e → ℂ) → Pairs N → ℂ) (b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), AnalyticAt ℂ z x₀ ∧ (∀ p q, AnalyticAt ℂ (fun x => b x p q) x₀) ∧ z x₀ = 0 ∧ (∀ᶠ x in 𝓝 x₀, (b x).BlockTriangular id ∧ IsUnit (b x).det ∧ g x = cellMat N (z x) * b x) ∧ ∀ v, fderiv ℂ z x₀ v = 0 ↔ ((g x₀)⁻¹ * Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | exact GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviForm
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PerDiag

variable {e N : ℕ}

def PlurRe (z0 : Fin e → ℂ) (f : (Fin e → ℂ) → ℝ) : Prop :=
  ∃ H : (Fin e → ℂ) → ℂ, AnalyticAt ℂ H z0 ∧ f =ᶠ[𝓝 z0] fun w => (H w).re

theorem PlurRe.zero (z0 : Fin e → ℂ) : PlurRe z0 fun _ => 0 :=
  ⟨fun _ => 0, analyticAt_const, by simp⟩

theorem PlurRe.congr {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (hf : f' =ᶠ[𝓝 z0] f) : PlurRe z0 f' := by
  obtain ⟨H, hH, hev⟩ := h
  exact ⟨H, hH, hf.trans hev⟩

theorem PlurRe.add {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w + f' w := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun w => H w + H' w, hH.fun_add hH', ?_⟩
  filter_upwards [hev, hev'] with w h1 h2
  simp [h1, h2]

theorem PlurRe.sub {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w - f' w := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun w => H w - H' w, hH.fun_sub hH', ?_⟩
  filter_upwards [hev, hev'] with w h1 h2
  simp [h1, h2]

theorem PlurRe.sum {z0 : Fin e → ℂ} {ι : Type} [Fintype ι] {f : ι → (Fin e → ℂ) → ℝ}
    (h : ∀ a, PlurRe z0 (f a)) : PlurRe z0 fun w => ∑ a, f a w := by
  choose H hH hev using h
  refine ⟨fun w => ∑ a, H a w, Finset.analyticAt_fun_sum _ fun a _ => hH a, ?_⟩
  filter_upwards [eventually_all.2 hev] with w hw
  simp [hw]

theorem plurRe_log_norm {z0 : Fin e → ℂ} {B : (Fin e → ℂ) → ℂ} (hB : AnalyticAt ℂ B z0)
    (h0 : B z0 ≠ 0) : PlurRe z0 fun w => Real.log ‖B w‖ := by
  have hq : AnalyticAt ℂ (fun w => B w / B z0) z0 := hB.fun_div analyticAt_const h0
  have hs : (fun w => B w / B z0) z0 ∈ Complex.slitPlane := by
    simp [h0]
  refine ⟨fun w => Complex.log (B w / B z0) + Complex.log (B z0),
    (hq.clog hs).fun_add analyticAt_const, ?_⟩
  filter_upwards [hB.continuousAt.eventually_ne h0] with w hw
  simp only [Complex.add_re, Complex.log_re, norm_div]
  rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 h0)]
  ring

def diagLog (b : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : ℝ :=
  ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0

theorem plurRe_diagLog {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (k : ℕ) :
    PlurRe z0 fun w => diagLog (b w) k := by
  refine PlurRe.sum fun a => ?_
  by_cases h : (a : ℕ) < k
  · simpa [h] using plurRe_log_norm (hb a) (h0 a)
  · simpa [h] using PlurRe.zero z0

def stepCorr (N j : ℕ) (i : Fin N) (b : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then diagLog b (N - j + ((i : ℕ) + 1)) - diagLog b (N - j)
  else diagLog b N - diagLog b (N - j) + diagLog b ((i : ℕ) + 1 - j)

theorem plurRe_stepCorr {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (j : ℕ) (i : Fin N) :
    PlurRe z0 fun w => stepCorr N j i (b w) := by
  have h := plurRe_diagLog hb h0
  by_cases hi : (i : ℕ) + 1 ≤ j
  · simpa [stepCorr, hi] using (h _).sub (h _)
  · simpa [stepCorr, hi] using ((h _).sub (h _)).add (h _)

theorem stepPot_unitary_mul {j : ℕ} {u : Matrix (Fin N) (Fin N) ℂ}
    (hu : gramOf (sigForm N j) u = diagonal fun i => ((sigForm N j i : ℝ) : ℂ))
    (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i (u * g) = stepPot N j i g := by
  have h k := (GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k g u 1).1 hu
  unfold stepPot
  simp only [h]

theorem stepPot_mul_triangular {j : ℕ} (hj : j ≤ N) {c b : Matrix (Fin N) (Fin N) ℂ}
    (hc : InFlagDomain N j c) (hb : b.BlockTriangular id) (hu : IsUnit b.det) (i : Fin N) :
    stepPot N j i (c * b) = stepPot N j i c + stepCorr N j i b := by
  have h k := (GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k c 1 b).2 hb hu ((GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors N j hj).2 c hc k)
  unfold stepPot stepCorr diagLog
  split_ifs <;> simp only [h] <;> ring

theorem inFlagDomain_base {j : ℕ} : InFlagDomain N j 1 := by
  refine ⟨by simp, ?_⟩
  have h : -gramHead (sigForm N j) (N - j) (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    by_cases hab : a = b
    · subst hab
      simp [gramHead, gramOf, sigForm, ha]
    · have : (⟨a, ha⟩ : {a : Fin N // (a : ℕ) < N - j}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
      simp [gramHead, gramOf, Matrix.one_apply, hab, this]
  rw [h]
  exact Matrix.PosDef.one

theorem continuous_cellMat (N : ℕ) : Continuous (cellMat N) := by
  unfold cellMat
  refine continuous_finsetSum _ fun k _ => (continuous_const_smul _).comp (Continuous.pow ?_ k)
  refine continuous_finsetSum _ fun p _ => ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.single_apply]
  split_ifs
  · exact continuous_apply p
  · exact continuous_const

theorem exists_cell_coords {j : ℕ} (hj : j ≤ N) (gc : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (z0 : Fin e → ℂ) (han : ∀ a b, AnalyticAt ℂ (fun w => gc w a b) z0)
    (hdom : ∀ᶠ w in 𝓝 z0, InFlagDomain N j (gc w)) :
    ∃ z : (Fin e → ℂ) → Pairs N → ℂ, AnalyticAt ℂ z z0 ∧ z z0 = 0 ∧
      (∀ i, PlurRe z0 fun w => stepPot N j i (gc w) - stepPot N j i (cellMat N (z w))) ∧
      ∀ v, fderiv ℂ z z0 v = 0 ↔
        ((gc z0)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v).BlockTriangular id := by
  obtain ⟨u, b₀, hu, hb₀, hdet, hub⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj (gc z0) hdom.self_of_nhds
  have hgu : IsUnit (gc z0).det := hdom.self_of_nhds.1
  have huu : IsUnit u.det := by
    have : u.det * (gc z0).det = b₀.det := by rw [← Matrix.det_mul, hub]
    rw [← this] at hdet
    exact isUnit_of_mul_isUnit_left hdet
  have han' : ∀ a b, AnalyticAt ℂ (fun w => (u * gc w) a b) z0 := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (han c b)
  obtain ⟨z, b, hz, hb, hz0, hev, hiff⟩ := GlobalTheory.T.local_bruhat_cell_analytic_coordinates e N (fun w => u * gc w) z0 han'
    (by simpa only [hub] using hb₀) (by simpa only [hub] using hdet)
  refine ⟨z, hz, hz0, fun i => ?_, fun v => ?_⟩
  · have hcell : ∀ᶠ w in 𝓝 z0, InFlagDomain N j (cellMat N (z w)) := by
      have hc : ContinuousAt (fun w => cellMat N (z w)) z0 :=
        (continuous_cellMat N).continuousAt.comp hz.continuousAt
      have hm : {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∈ 𝓝 (cellMat N (z z0)) := by
        rw [hz0, cellMat_zero N]
        exact (GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors N j hj).1.mem_nhds inFlagDomain_base
      exact hc hm
    obtain ⟨ht, hdb, -⟩ := hev.self_of_nhds
    have hd0 : ∀ a, b z0 a a ≠ 0 := by
      intro a h
      rw [Matrix.det_of_upperTriangular ht] at hdb
      exact hdb.ne_zero (Finset.prod_eq_zero (Finset.mem_univ a) h)
    refine (plurRe_stepCorr (fun a => hb a a) hd0 j i).congr ?_
    filter_upwards [hev, hcell] with w ⟨h1, h2, h3⟩ hw
    rw [← stepPot_unitary_mul hu i (gc w), h3, stepPot_mul_triangular hj hw h1 h2 i]
    ring
  · have hD : (Matrix.of fun a b => fderiv ℂ (fun w => (u * gc w) a b) z0 v) =
        u * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v := by
      ext a b
      have h1 : HasFDerivAt (fun w => ∑ c, u a c * gc w c b)
          (∑ c, u a c • fderiv ℂ (fun w => gc w c b) z0) z0 :=
        HasFDerivAt.fun_sum fun c _ => ((han c b).differentiableAt.hasFDerivAt).const_mul (u a c)
      simp only [Matrix.of_apply, Matrix.mul_apply]
      rw [h1.fderiv]
      simp
    rw [hiff v, hD, Matrix.mul_inv_rev]
    have : (gc z0)⁻¹ * u⁻¹ * (u * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v) =
        (gc z0)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u⁻¹, Matrix.nonsing_inv_mul _ huu, Matrix.one_mul]
    rw [this]

def rel (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

theorem levi_of_cell {j : ℕ} (hj : j ≤ N) (i : Fin N) {z0 : Fin e → ℂ} {f : (Fin e → ℂ) → ℝ}
    {z : (Fin e → ℂ) → Pairs N → ℂ} (hz : AnalyticAt ℂ z z0) (hz0 : z z0 = 0)
    (hf : PlurRe z0 fun w => f w - stepPot N j i (cellMat N (z w))) :
    ContDiffAt ℝ 2 f z0 ∧ ∀ v, levi f z0 v = ∑ p : Pairs N,
      if min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2)
      then (1 / 2 : ℝ) * ‖fderiv ℂ z z0 v p‖ ^ 2 else 0 := by
  obtain ⟨H, hH, hev⟩ := hf
  let φ : (Pairs N → ℂ) → ℝ := fun y => stepPot N j i (cellMat N y)
  have hφ : ContDiffAt ℝ 2 φ 0 := (GlobalTheory.T.flag_potential_levi_form_cell N j hj i 0).1
  have hφ' : ContDiffAt ℝ 2 φ (z z0) := by rwa [hz0]
  have hzR : ContDiffAt ℝ 2 z z0 := (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc : ContDiffAt ℝ 2 (φ ∘ z) z0 := hφ'.comp z0 hzR
  have hHR : ContDiffAt ℝ 2 (fun w => (H w).re) z0 :=
    Complex.reCLM.contDiff.contDiffAt.comp z0 ((hH.restrictScalars (𝕜 := ℝ)).contDiffAt)
  have hfe : f =ᶠ[𝓝 z0] fun w => (φ ∘ z) w + 1 * (H w).re := by
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, φ, one_mul]
    linarith
  refine ⟨(hc.add (contDiffAt_const.mul hHR)).congr_of_eventuallyEq hfe, fun v => ?_⟩
  rw [levi_congr hfe v, levi_add_smul 1 hc hHR v, levi_comp v hz hφ', levi_re_analytic hH v, hz0]
  have hlev := (GlobalTheory.T.flag_potential_levi_form_cell N j hj i (fderiv ℂ z z0 v)).2
  simp [φ, rel] at hlev ⊢
  exact hlev

theorem rel_lt {j : ℕ} (hj : j ≤ N) (a : Fin N) : rel N j a < N := by
  have := a.2
  unfold rel
  split_ifs <;> omega

def relF {j : ℕ} (hj : j ≤ N) (a : Fin N) : Fin N := ⟨rel N j a, rel_lt hj a⟩

theorem relF_injective {j : ℕ} (hj : j ≤ N) : Function.Injective (relF (N := N) hj) := by
  intro a b h
  have h' : rel N j a = rel N j b := congrArg Fin.val h
  have ha := a.2
  have hb := b.2
  unfold rel at h'
  ext
  split_ifs at h' <;> omega

def pairMap (σ : Fin N → Fin N) (hσ : Function.Injective σ) (p : Pairs N) : Pairs N :=
  ⟨(min (σ p.1.1) (σ p.1.2), max (σ p.1.1) (σ p.1.2)), min_lt_max.2 (hσ.ne p.2.ne)⟩

theorem pairMap_injective (σ : Fin N → Fin N) (hσ : Function.Injective σ) :
    Function.Injective (pairMap σ hσ) := by
  rintro ⟨⟨p₁, p₂⟩, hp⟩ ⟨⟨q₁, q₂⟩, hq⟩ h
  have h1 : min (σ p₁) (σ p₂) = min (σ q₁) (σ q₂) := congrArg (fun t : Pairs N => t.1.1) h
  have h2 : max (σ p₁) (σ p₂) = max (σ q₁) (σ q₂) := congrArg (fun t : Pairs N => t.1.2) h
  have hp' : p₁ < p₂ := hp
  have hq' : q₁ < q₂ := hq
  rcases le_total (σ p₁) (σ p₂) with a | a <;> rcases le_total (σ q₁) (σ q₂) with c | c
  · rw [min_eq_left a, min_eq_left c] at h1
    rw [max_eq_right a, max_eq_right c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    rfl
  · rw [min_eq_left a, min_eq_right c] at h1
    rw [max_eq_right a, max_eq_left c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    exact absurd hp' (not_lt.2 hq'.le)
  · rw [min_eq_right a, min_eq_left c] at h1
    rw [max_eq_left a, max_eq_right c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    exact absurd hp' (not_lt.2 hq'.le)
  · rw [min_eq_right a, min_eq_right c] at h1
    rw [max_eq_left a, max_eq_left c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    rfl

def pairEquiv {j : ℕ} (hj : j ≤ N) : Pairs N ≃ Pairs N :=
  Equiv.ofBijective (pairMap (relF hj) (relF_injective hj))
    (pairMap_injective _ _).bijective_of_finite

theorem pairEquiv_fst_le {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    (pairEquiv hj p).1.1 ≤ i ↔ min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) := by
  change min (relF hj p.1.1) (relF hj p.1.2) ≤ i ↔ _
  rw [min_le_iff, min_le_iff]
  rfl

theorem pairEquiv_lt_snd {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    i < (pairEquiv hj p).1.2 ↔ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2) := by
  change i < max (relF hj p.1.1) (relF hj p.1.2) ↔ _
  rw [lt_max_iff, lt_max_iff]
  rfl

end PerDiag


open PerDiag in
theorem levi_diagonal_of_isPeriodChart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) := by
  intro e X _ A Ψ _ _ N j hj pot x V g hP k hx
  obtain ⟨hV, hxV, hhol, hdom, hpot⟩ := hP
  have hsx : (A.chart k).symm (A.chart k x) = x := (A.chart k).left_inv hx
  have hmem : A.chart k x ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hx, by simpa [hsx] using hxV⟩
  have hnhds : (A.chart k).target ∩ (A.chart k).symm ⁻¹' V ∈ 𝓝 (A.chart k x) :=
    ((A.chart k).isOpen_inter_preimage_symm hV).mem_nhds hmem
  have hcell := fun τ => exists_cell_coords hj (fun w => g τ ((A.chart k).symm w)) (A.chart k x)
    (fun a b => hhol τ a b k _ hmem)
    (by filter_upwards [hnhds] with w hw using hdom τ _ hw.2)
  choose z hz hz0 hstep hiff using hcell
  have key := fun p : Ψ × Fin N => levi_of_cell (f := (pot p).φ x ∘ (A.chart k).symm) hj p.2 (hz p.1)
    (hz0 p.1) (by
      obtain ⟨G, hG, hφ⟩ := hpot p
      have h1 : PlurRe (A.chart k x) fun w => (pot p).φ x ((A.chart k).symm w) -
          stepPot N j p.2 (g p.1 ((A.chart k).symm w)) := by
        refine ⟨G ∘ (A.chart k).symm, hG k _ hmem, ?_⟩
        filter_upwards [hnhds] with w hw
        rw [hφ _ hw.2]
        simp
      refine (h1.add (hstep p.1 p.2)).congr (Eventually.of_forall fun w => ?_)
      simp)
  let ρ := pairEquiv (N := N) hj
  let Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ) :=
    { toFun := fun v q => fderiv ℂ (z q.1) (A.chart k x) v (ρ.symm q.2)
      map_add' := fun v w => by ext q; simp
      map_smul' := fun c v => by ext q; simp }
  refine ⟨Lm, fun p => (key p).1, fun p v => ?_, fun hI => ?_⟩
  · rw [(key p).2 v]
    refine Eq.trans ?_ (Equiv.sum_comp ρ _)
    refine Finset.sum_congr rfl fun q _ => ?_
    have e3 : Lm v (p.1, ρ q) = fderiv ℂ (z p.1) (A.chart k x) v q := by simp [Lm]
    simp only [e3, pairEquiv_fst_le, ρ, pairEquiv_lt_snd]
  · refine (injective_iff_map_eq_zero Lm).2 fun v hv => ?_
    refine hI k hx v fun τ => ?_
    have h0 : fderiv ℂ (z τ) (A.chart k x) v = 0 := by
      funext q
      have := congrFun hv (τ, ρ q)
      simpa [Lm] using this
    have := (hiff τ v).1 h0
    rwa [hsx] at this

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviFormStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_chart_potential_levi_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart | exact GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecond
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := by
  intro c z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart c).symm z))
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart c).symm) z := hh.2 c k z ⟨hz.1, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart c).symm) z) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k (h ((B.chart c).symm z))) ∈ V
      rw [(A.chart k).left_inv hk]; exact hz.2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (h ∘ (B.chart c).symm) z :=
    hh.1.continuousAt.comp ((B.chart c).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  have hu' : h ((B.chart c).symm u) ∈ (A.chart k).source := hu
  simp only [Function.comp]
  rw [(A.chart k).left_inv hu']

theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  refine ⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane,
    ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane,
    ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖,
    fun k u hu => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

end Holo

theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  have hu : IsUnit H.det := hd.isUnit
  have h1 := ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu] at h1
  have h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold detFac
    split_ifs <;> simp [minorIJ_one_self]
  intro h0
  rw [h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := GlobalTheory.T.period_chart_potential_levi_form e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem stepWeight_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM p Kk _ ιk _ κ v hb hr e R pr hp B h1 hpot hsec hsnc had
  have hyp : IsStepHyp M BM p κ v R pr := ⟨hb, hr, hp, h1⟩
  have hc := GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp
  have hfs : IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) :=
    (GlobalTheory.T.log_resolution_fubini_study_positive Kk ιk _ e R).1 _ (GlobalTheory.T.fubini_study_metric_smooth Kk ιk _)
  have hnorm : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  have hsm := GlobalTheory.T.flag_gap_holomorphic_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hps := GlobalTheory.T.flag_gap_holomorphic_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.flag_gap_holomorphic_pullback_third K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hgr := GlobalTheory.T.flag_gap_holomorphic_pullback_fourth K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.singular_potential_log_growth_psh e R.X R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm _ (stepPh M BM p v R pr) C₁ hfs hsm hps hC₁
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local e R.X R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm had (stepPh M BM p v R pr) hsm hgr
  refine ⟨stepPh M BM p v R pr, max C₂ C₃, ?_, ?_, ?_, hC₃ _ (le_max_right _ _)⟩
  · intro x hx z hz hzv
    have := GlobalTheory.T.flag_gap_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x z (R.mem_U x) hx hz hzv
    rw [this, stepGap]
    ring
  · intro x x' hxx hk
    exact GlobalTheory.T.flag_gap_pullback_second K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x' hxx hk
  · obtain ⟨h1', h2', h3', h4'⟩ := hC₂
    refine ⟨h1', h2', h3', fun x hx => ?_⟩
    have hlog : 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
      apply Real.log_nonneg
      have := hnorm x
      have h2 := Real.add_one_le_exp (1 : ℝ)
      unfold rW
      linarith
    obtain ⟨ha, hb'⟩ := h4' x hx
    refine ⟨?_, hb'.trans (le_max_left _ _)⟩
    have : -max C₂ C₃ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) ≤
        -C₂ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) hlog
    exact this.trans ha

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLineStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_flag_bundle_metric_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | exact GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists <;> assumption)
end
