module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
namespace GlobalTheory.CompanionTheory.RgEisDGood

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem gauss_bound (b c : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3 ≤ M := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max |b| |c| := ⟨_, rfl⟩
  have hbB : |b| ≤ B := hB ▸ le_max_left _ _
  have hcB : |c| ≤ B := hB ▸ le_max_right _ _
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hbB
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + B := ⟨_, rfl⟩
  have hT : 1 ≤ T := by linarith
  refine ⟨16 * T ^ 4 * Real.exp (B ^ 2), by positivity, fun z h1 h2 => ?_⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = z.re := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = z.im := ⟨_, rfl⟩
  have hx : |x| ≤ B := by
    rw [abs_le]
    constructor
    · have := neg_abs_le b
      rw [hxdef]; linarith
    · have := le_abs_self c
      rw [hxdef]; linarith
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
  have hnorm : ‖Complex.exp (z ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, hxdef, hydef]
  have hz : ‖z‖ ≤ |x| + |y| := by
    rw [hxdef, hydef]; exact Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = T + |y| := ⟨_, rfl⟩
  have hy0 := abs_nonneg y
  have hu1 : 1 ≤ u := by linarith
  have h1z : 1 + ‖z‖ ≤ u := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (y ^ 2 / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ Real.exp_pos _
  have hE : 1 + y ^ 2 / 2 ≤ E := by
    have := Real.add_one_le_exp (y ^ 2 / 2)
    rw [hEdef]; linarith
  have hEE : E ^ 2 = Real.exp (y ^ 2) := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu2 : u ^ 2 ≤ 4 * T ^ 2 * E := by
    have hsq : |y| ^ 2 = y ^ 2 := sq_abs y
    have hA : u ^ 2 ≤ 2 * T ^ 2 + 2 * y ^ 2 := by
      rw [hudef]
      nlinarith [sq_nonneg (T - |y|)]
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hC : 2 * T ^ 2 + 2 * y ^ 2 ≤ 4 * T ^ 2 * (1 + y ^ 2 / 2) := by
      nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.2 hT2), sq_nonneg T]
    have hD : 4 * T ^ 2 * (1 + y ^ 2 / 2) ≤ 4 * T ^ 2 * E :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have hu4 : u ^ 4 ≤ 16 * T ^ 4 * Real.exp (y ^ 2) := by
    have h := pow_le_pow_left₀ (by positivity) hu2 2
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ ≤ (4 * T ^ 2 * E) ^ 2 := h
      _ = 16 * T ^ 4 * E ^ 2 := by ring
      _ = 16 * T ^ 4 * Real.exp (y ^ 2) := by rw [hEE]
  have hz3 : (1 + ‖z‖) ^ 3 ≤ u ^ 4 := by
    have h0 : 0 ≤ 1 + ‖z‖ := by positivity
    calc (1 + ‖z‖) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ h0 h1z 3
      _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hexp : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (B ^ 2) * Real.exp (-y ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  rw [hnorm]
  calc Real.exp (x ^ 2 - y ^ 2) * (1 + ‖z‖) ^ 3
      ≤ (Real.exp (B ^ 2) * Real.exp (-y ^ 2)) * (16 * T ^ 4 * Real.exp (y ^ 2)) :=
        mul_le_mul hexp (hz3.trans hu4) (by positivity) (by positivity)
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) * (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) := by ring
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) := by
        rw [← Real.exp_add]; simp

theorem dGood : DGood := by
  intro a N ha
  obtain ⟨hd, hg⟩ := ha
  have hE : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * a z :=
    (Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul hd
  have key : ∀ b c : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖) ≤ M := by
    intro b c
    obtain ⟨M₁, hM₁, h₁⟩ := gauss_bound b c
    obtain ⟨M₂, h₂⟩ := hg b c
    refine ⟨|M₂| * M₁, by positivity, fun z hb hc => ?_⟩
    have hz := h₁ z hb hc
    have ha' : ‖a z‖ ≤ |M₂| * (1 + ‖z‖) ^ 2 :=
      (h₂ z hb hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    rw [norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖a z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (|M₂| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M₂| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3) := by ring
      _ ≤ |M₂| * M₁ := by gcongr
  refine ⟨⟨hE, fun b c => ?_⟩, ⟨(differentiable_id.sub_const N).mul hE, fun b c => ?_⟩⟩
  · obtain ⟨M, _, h⟩ := key b c
    refine ⟨M, fun z hb hc => (?_ : _ ≤ _).trans (h z hb hc)⟩
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])
  · obtain ⟨M, hM, h⟩ := key b c
    refine ⟨(1 + ‖N‖) * M, fun z hb hc => ?_⟩
    have hzN : ‖z - N‖ ≤ (1 + ‖N‖) * (1 + ‖z‖) := by
      have := norm_sub_le z N
      nlinarith [norm_nonneg z, norm_nonneg N, mul_nonneg (norm_nonneg z) (norm_nonneg N)]
    rw [norm_mul]
    calc ‖z - N‖ * ‖Complex.exp (z ^ 2) * a z‖
        ≤ ((1 + ‖N‖) * (1 + ‖z‖)) * ‖Complex.exp (z ^ 2) * a z‖ := by gcongr
      _ = (1 + ‖N‖) * (‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖)) := by ring
      _ ≤ (1 + ‖N‖) * M := by
          have := h z hb hc
          gcongr

end GlobalTheory.CompanionTheory.RgEisDGood
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGoodStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_term_good : DGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisDGood.dGood | exact GlobalTheory.CompanionTheory.RgEisDGood.dGood | (intros; apply GlobalTheory.CompanionTheory.RgEisDGood.dGood <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportSmallF
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestBump

variable {ι : Type} [Fintype ι]

def nsq (y : ι → ℂ) : ℝ := ∑ j, ‖y j‖ ^ 2

lemma contDiff_coordSq (i : ι) {n : WithTop ℕ∞} : ContDiff ℝ n fun y : ι → ℂ => ‖y i‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i)

lemma contDiff_nsq {n : WithTop ℕ∞} : ContDiff ℝ n (nsq : (ι → ℂ) → ℝ) :=
  ContDiff.sum fun j _ => contDiff_coordSq j

lemma coordSq_le_nsq (y : ι → ℂ) (i : ι) : ‖y i‖ ^ 2 ≤ nsq y :=
  Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

lemma nsq_smul (t : ℂ) (v : ι → ℂ) : nsq (t • v) = ‖t‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

def radial : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma radial_one : radial 1 = 1 :=
  radial.one_of_mem_closedBall (Metric.mem_closedBall_self radial.rIn_pos.le)

lemma radial_zero_of_le {x : ℝ} (h : x ≤ 1 / 2) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

lemma radial_zero_of_ge {x : ℝ} (h : 3 / 2 ≤ x) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

def angular {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

lemma angular_one {δ : ℝ} (hδ : 0 < δ) : angular hδ 1 = 1 :=
  (angular hδ).one_of_mem_closedBall (Metric.mem_closedBall_self (angular hδ).rIn_pos.le)

lemma lt_of_angular_ne {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (h : angular hδ x ≠ 0) : 1 - δ < x := by
  by_contra hx
  refine h ((angular hδ).zero_of_le_dist ?_)
  rw [Real.dist_eq, abs_of_nonpos (by linarith [not_lt.1 hx])]
  change δ ≤ _
  linarith [not_lt.1 hx]

def bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) (y : ι → ℂ) : ℝ :=
  radial (nsq y) * angular hδ (‖y i₀‖ ^ 2 / nsq y)

def smallF (t : ℂ) : ℝ := radial (‖t‖ ^ 2)

lemma contDiff_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ (n : WithTop ℕ∞) (bigF i₀ hδ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases h : 0 < nsq y
  · exact (radial.contDiff.contDiffAt.comp y contDiff_nsq.contDiffAt).mul
      ((angular hδ).contDiff.contDiffAt.comp y
        ((contDiff_coordSq i₀).contDiffAt.div contDiff_nsq.contDiffAt h.ne'))
  · have h0 : nsq y < 1 / 2 := by linarith [not_lt.1 h]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(contDiff_nsq (n := 0)).continuous.continuousAt.eventually (gt_mem_nhds h0)] with z hz
    simp [bigF, radial_zero_of_le (le_of_lt hz)]

lemma hasCompactSupport_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (bigF i₀ hδ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 2) fun y hy => ?_
  by_contra hne
  have hr : radial (nsq y) ≠ 0 := fun h => hne (by simp [bigF, h])
  have hlt : nsq y < 3 / 2 := by
    by_contra hge
    exact hr (radial_zero_of_ge (not_lt.1 hge))
  refine hy ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have := coordSq_le_nsq y i
  nlinarith [norm_nonneg (y i)]

lemma contDiff_smallF {n : ℕ∞} : ContDiff ℝ (n : WithTop ℕ∞) smallF :=
  radial.contDiff.comp (contDiff_norm_sq ℝ)

lemma hasCompactSupport_smallF : HasCompactSupport smallF := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun t ht => ?_
  refine radial_zero_of_ge ?_
  have : 2 < ‖t‖ := by simpa using ht
  nlinarith

end GlobalTheory.CompanionTheory.TestBump


open GlobalTheory.CompanionTheory.TestBump in
theorem GlobalTheory.CompanionTheory.TestBump.cplxBump : CplxBump := by
  classical
  intro ι _ _ i₀ δ hδ
  refine ⟨bigF i₀ hδ, smallF, contDiff_bigF i₀ hδ, hasCompactSupport_bigF i₀ hδ, contDiff_smallF,
    hasCompactSupport_smallF, ?_, ?_, fun t => radial.nonneg, fun v => mul_nonneg radial.nonneg (angular hδ).nonneg, ?_⟩
  · have h1 : nsq (Pi.single i₀ 1 : ι → ℂ) = 1 := by
      simp only [nsq]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    simp [bigF, h1, radial_one, angular_one]
  · intro t ht
    simp [smallF, ht, radial_one]
  · intro v hv
    have hv1 : nsq v = 1 := hv
    have hFv : bigF i₀ hδ v = angular hδ (‖v i₀‖ ^ 2) := by
      simp [bigF, hv1, radial_one]
    refine ⟨fun t => ?_, fun h => ?_⟩
    · rw [hFv]
      by_cases ht : t = 0
      · subst ht
        have hz : radial (0 : ℝ) = 0 := radial_zero_of_le (by norm_num)
        simp [bigF, smallF, nsq, hz]
      · have hn : nsq (t • v) = ‖t‖ ^ 2 := by rw [nsq_smul, hv1, mul_one]
        have ht2 : ‖t‖ ^ 2 ≠ 0 := by positivity
        simp only [bigF, smallF, hn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
        rw [mul_div_cancel_left₀ _ ht2]
    · exact lt_of_angular_ne hδ (by rwa [hFv] at h)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisAvg

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem pointwise_bound {K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {φ : K → ℂ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ κ, ‖ρ κ‖ ≤ M) (hc : ∀ p ∈ P, ‖c p‖ = 1) (hL : Law K P c φ)
    (hN : Near K P {v | ‖ρ v - 1‖ ≤ 1 / (4 * M)} φ) {w : W} (hw : w ∈ secSp K P c ρ) (κ : K) :
    ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2 := by
  by_cases h0 : φ κ = 0
  · simp [h0]
  obtain ⟨r, v, hr, hv, rfl, hn⟩ := hN κ h0
  have hM0 : 0 < M := by linarith
  have hcr : ‖c r‖ = 1 := hc _ hr
  have hφ : φ (r * v) = c r * φ v := hL r v hr
  have hnorm : ‖φ (r * v)‖ = ‖φ v‖ := by rw [hφ, norm_mul, hcr, one_mul]
  have hwr : c r • ρ r w = w := hw r hr
  obtain ⟨u, hu⟩ : ∃ u, u = ρ v w - w := ⟨_, rfl⟩
  have hub : ‖u‖ ≤ ‖w‖ / (4 * M) := by
    have h1 : u = (ρ v - 1) w := by simp [hu]
    have hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M) := hv
    rw [h1]
    calc ‖(ρ v - 1) w‖ ≤ ‖ρ v - 1‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (4 * M) * ‖w‖ := by gcongr
      _ = ‖w‖ / (4 * M) := by ring
  have hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4 := by
    rw [norm_smul, hcr, one_mul]
    calc ‖ρ r u‖ ≤ ‖ρ r‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (‖w‖ / (4 * M)) := by
          gcongr
          exact hM r
      _ = ‖w‖ / 4 := by field_simp
  have hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w =
      (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u) := by
    have h2 : ρ v w = w + u := by simp [hu]
    have h3 : ρ (r * v) w = ρ r w + ρ r u := by
      rw [map_mul, ContinuousLinearMap.mul_apply, h2, map_add (f := _)]
    rw [hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]
    abel
  rw [hexp, hnorm]
  calc ‖(φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)‖
      ≤ ‖φ v - ((‖φ v‖ : ℝ) : ℂ)‖ * ‖w‖ + ‖φ v‖ * ‖c r • ρ r u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr
    _ = ‖φ v‖ * ‖w‖ / 2 := by ring

theorem avg_sub_bound [FiniteDimensional ℂ W] {K : Subgroup G} [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {φ : K → ℂ} (hφ : Continuous φ) (w : W)
    (h : ∀ κ, ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2) :
    ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hint : Integrable (fun κ => φ κ • ρ κ) μ :=
    (hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun κ => ‖φ κ‖) μ :=
    hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun κ => φ κ • ρ κ w) μ := by
    have := hint.apply_continuousLinearMap w
    exact this
  have hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ :=
    (hint2.ofReal (𝕜 := ℂ)).smul_const w
  have e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ := ContinuousLinearMap.integral_apply hint w
  have e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ := by
    rw [integral_smul_const, integral_complex_ofReal]
  rw [e1, e2, ← integral_sub hint3 hint4]
  have e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ := by
    rw [integral_div, integral_mul_const]
  rw [e3]
  exact norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)

theorem mass_pos {K : Subgroup G} [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [IsTopologicalGroup K] (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {φ : K → ℂ} (hφ : Continuous φ) (h1 : φ 1 = 1) : 0 < ∫ κ, ‖φ κ‖ ∂μ := by
  refine hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_
  simp [h1]

end Abstract

theorem avgInv_of_avgMem : AvgMem → AvgInv := by
  intro hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI := hH
  haveI := hP
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_range hρ).isBounded.exists_norm_le
    exact ⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩
  · have ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0) := by
      have h5 := hρ.tendsto (1 : K)
      rw [map_one] at h5
      simpa using h5.sub_const 1
    have h4 : (0 : ℝ) < 1 / (4 * M) := by positivity
    filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv
    simpa using hv
  · intro φ hφ h1 hL hN
    have hI : 0 < ∫ κ, ‖φ κ‖ ∂μ := mass_pos μ hφ h1
    have hb : ∀ w ∈ secSp K P c ρ,
        ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := fun w hw =>
      avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)
    have hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ := fun w =>
      hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w
    let T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ :=
      ((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun w hw => ?_
      have h0 : avg μ ρ φ (w : W) = 0 := congrArg Subtype.val hw
      have h6 := hb w w.2
      rw [h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le] at h6
      have h7 : ‖(w : W)‖ = 0 := by
        have h8 : 0 ≤ ‖(w : W)‖ := norm_nonneg _
        nlinarith
      exact Subtype.ext (norm_eq_zero.mp h7)
    let e := LinearEquiv.ofInjectiveEndo T hinj
    refine ⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply w)

end GlobalTheory.CompanionTheory.RgEisAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvarianceStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariance : AvgMem → AvgInv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | exact GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | (intros; apply GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {G : Type} [Group G] [TopologicalSpace G]
  {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem one_toIdele_lemma (y : IdeleGroup k) :
    (((1 : HeckeCharacter k).toIdele y : Circle) : ℂ) = 1 := by
  first
  | rfl
  | simp [HeckeCharacter.toIdele]

theorem side_one {π : G →* GL ι 𝔸[k]} {Γ K P : Subgroup G} {i : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η : G → ℝ} (hs : Side π Γ K P i ω d c η) :
    Side π Γ K P i (1 : HeckeCharacter k) d (1 : G → ℂ) η := by
  refine ⟨hs.two, mul_one 1, hs.cont, hs.piK, hs.piΓ, hs.trans, hs.mem,
    ⟨hs.par.closed, hs.par.iwa, ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl,
      continuous_one.continuousOn⟩⟩, hs.ht, fun p hp => ⟨?_, (hs.val p hp).2⟩⟩
  exact (one_toIdele_lemma _).symm

theorem norm_globalZeta_le (F : 𝔸[k] → ℂ) (x : ℝ) :
    ‖globalZeta F (1 : HeckeCharacter k) x‖ ≤
      ∫ t : IdeleGroup k, ‖F (t : 𝔸[k])‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ∂ideleMeasure k := by
  unfold GroundTheory.Global.globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_mul, norm_mul, one_toIdele_lemma, norm_one, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k t).2, Complex.ofReal_re]

private theorem stab_lemma {R : Type} [CommRing R] (h : GL ι R) (i : ι) (a b : R)
    (h1 : (h : Matrix ι ι R).mulVec (Pi.single i 1) = a • Pi.single i 1)
    (h2 : ((h⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = b • Pi.single i 1) :
    h ∈ stab R {i} := by
  show ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
    (h : Matrix ι ι R) r c = 0 ∧ ((h⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  rw [Set.mem_singleton_iff] at hc hr
  subst hc
  constructor
  · have := congrFun h1 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this
  · have := congrFun h2 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this

private theorem stab_lemma_2 {R : Type} [CommRing R] (X Y : GL ι R) (i : ι) (c₁ c₂ : Rˣ)
    (h : (c₁ : R) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      (c₂ : R) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)) :
    Y * X⁻¹ ∈ stab R {i} := by
  have hX : ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₁⁻¹ : R) * c₂) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]
  have hY : ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₂⁻¹ : R) * c₁) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, h, smul_smul, Units.inv_mul, one_smul]
  apply stab_lemma (Y * X⁻¹) i ((↑c₁⁻¹ : R) * c₂) ((↑c₂⁻¹ : R) * c₁)
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Units.mul_inv, Matrix.one_mulVec]
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem vec_mul_lemma_3 (A B : GL ι 𝔸[k]) (i : ι) :
    vec (A * B) i = ((B⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec A i) := by
  unfold PositivityTheory.RgEis.MG.vec
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem sideConv : EpConv → TestSph → Lines → Term → SideConv := by
  intro hEp hTest hLines hTerm
  unfold PositivityTheory.RgEis.MG.SideConv
  intro G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hs x hx
  unfold PositivityTheory.RgEis.Conv
  intro g
  have hs1 := side_one hs
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two
  have hx1 : (1 : ℝ) < x := by linarith
  obtain ⟨Ψ, Ψ₁, hΨ, -, -, hsph, hZ⟩ := hTest k ι i
  obtain ⟨-, hT⟩ := hTerm G K hK k ι π Γ P i 1 d 1 η hs1
  obtain ⟨hline, -, hscale⟩ := hT Ψ (x : ℂ)
  obtain ⟨e, he⟩ := hLines G K hK k ι π Γ P i ω d c η hs
  obtain ⟨-, hconv⟩ := hEp k ι Ψ hΨ
  obtain ⟨u, hu, hub⟩ := hconv x {(π g * dgl d)⁻¹} (max_lt hx1 hx) isCompact_singleton
  have hzt : ∀ κ ∈ K, zt π d i Ψ (1 : HeckeCharacter k) (x : ℂ) κ =
      globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ) := by
    intro κ hκ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) (1 : HeckeCharacter k) (x : ℂ) = _
    congr 1
    funext t
    exact hsph t ⟨kap π d κ, hs.piK κ hκ⟩
  have hA : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ =
        Real.exp (x * η (rep q * g)) * (‖modPow (d i) (x : ℂ)‖ *
          ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖) := by
    intro q
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hs.par.iwa (rep q * g)
    have hη : η (p * κ) = η p := by
      rw [hs.ht.left p hp κ]
      have h1 : η κ = η 1 := by simpa using hs.ht.right 1 κ hκ
      rw [h1, hs.ht.rat 1 (one_mem Γ) (one_mem P), add_zero]
    rw [hpk, hline p hp κ hκ, hzt κ hκ, hη, norm_mul, norm_mul, norm_mul, norm_mul,
      one_toIdele_lemma, Pi.one_apply, norm_one, one_mul, one_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal]
  have hApos : 0 < ‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖ := by
    refine mul_pos ?_ (norm_pos_iff.mpr (hZ x hx1))
    unfold GroundTheory.Automorphic.GodementSection.modPow
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k (d i)).2]
    exact Real.rpow_pos_of_pos (IdeleGroup.ideleModule k (d i)).2 _
  have hbound : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ ≤ u (e q) := by
    intro q
    obtain ⟨a, Ha⟩ := he q
    have hw : vec (π (rep q * g) * dgl d) i =
        (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec (π (rep q)) i) := by
      rw [map_mul, mul_assoc, vec_mul_lemma_3]
    rw [← hscale a, hw, ← Matrix.mulVec_smul, ← Ha]
    exact (norm_globalZeta_le (fun t => Ψ (t • (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) :
      Matrix ι ι 𝔸[k]).mulVec (ratV (e q).rep))) x).trans (hub _ rfl (e q))
  have hinj : Function.Injective e := by
    intro q₁ q₂ heq
    obtain ⟨a₁, H₁⟩ := he q₁
    obtain ⟨a₂, H₂⟩ := he q₂
    rw [heq] at H₁
    have key : ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₁ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₁))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) =
        ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₂ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₂))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) :=
      H₁.symm.trans H₂
    have hst := stab_lemma_2 (π (rep q₁)) (π (rep q₂)) i _ _ key
    rw [← map_inv, ← map_mul] at hst
    have hP := (hs.mem _).mpr hst
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hP))
  refine Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) (fun q => ?_)
    ((hu.comp_injective hinj).div_const (‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖))
  show Real.exp (x * η (rep q * g)) ≤ u (e q) / _
  rw [le_div_iff₀ hApos, ← hA q]
  exact hbound q

end GlobalTheory.CompanionTheory.RgEisSide
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergenceStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOHOfMemIntAd
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisCol

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem col_apply (i₀ : ι) (κ : GL ι 𝔸[k]) (j : ι) :
    TF.col i₀ κ j = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
  unfold TF.col
  rw [Matrix.mulVec_single_one]
  rfl

def finPart : 𝔸[k] →+* FiniteAdeleRing (𝓞 k) k := RingHom.snd _ _

theorem mem_OH_of_mem_intAd {x : 𝔸[k]} (hx : x ∈ intAd k) : x.2 ∈ OH k := by
  rw [mem_integralFiniteAdeles]
  intro v
  have := (Subring.mem_iInf.1 hx) v
  exact this

theorem sum_norm_sq {g : GL ι 𝔸[k]} {w : InfinitePlace k}
    (hg : (g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w) ∈ Matrix.unitaryGroup ι ℂ) (i₀ : ι) :
    ∑ j, ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hg) i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, (star ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w))) i₀ j *
      ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w)) j i₀ =
      ((‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have e : ‖(adStd k).φ w ((g : Matrix ι ι 𝔸[k]) j i₀)‖ = ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    rw [← e, Matrix.star_apply, Matrix.map_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp only [h2] at h
  exact_mod_cast h

theorem stab_entry {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) {j : ι} (hj : j ≠ i₀) :
    (p : Matrix ι ι 𝔸[k]) j i₀ = 0 ∧ ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ = 0 :=
  hp j hj i₀ rfl

theorem stab_mul_inv {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (p : Matrix ι ι 𝔸[k]) i₀ i₀ * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ = 1 := by
  have h : ((p : Matrix ι ι 𝔸[k]) * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀] at h
  · exact h
  · intro j _ hj
    rw [(stab_entry hp hj).2, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem bdet_single {R : Type} [CommRing R] {p : GL ι R} {i₀ : ι} (hu : IsUnit ((p : Matrix ι ι R) i₀ i₀)) :
    ((bdet {i₀} p : Rˣ) : R) = (p : Matrix ι ι R) i₀ i₀ := by
  have key : ∀ (i₁ : DecidableEq ({i₀} : Set ι)) (i₂ : Fintype ({i₀} : Set ι)),
      @Matrix.det _ i₁ i₂ R _ ((p : Matrix ι ι R).submatrix (Subtype.val : ({i₀} : Set ι) → ι) Subtype.val) =
        (p : Matrix ι ι R) i₀ i₀ := fun i₁ i₂ =>
    @Matrix.det_eq_elem_of_subsingleton _ i₁ i₂ R _ _ _ (⟨i₀, rfl⟩ : ({i₀} : Set ι))
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, key]
  · rw [key] at h
    exact absurd hu h

theorem bdet_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ((bdet {i₀} p : 𝔸[k]ˣ) : 𝔸[k]) = (p : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  bdet_single (IsUnit.of_mul_eq_one _ (stab_mul_inv hp))

theorem bdet_inv_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) = ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_val hp]; exact stab_mul_inv hp)

theorem col_mul {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) (κ : GL ι 𝔸[k]) :
    TF.col i₀ (p * κ) = (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • TF.col i₀ κ := by
  have h : ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 =
      ((((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k])) • (Pi.single i₀ 1 : ι → 𝔸[k]) := by
    ext1 j
    have e : (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1) j =
        ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e, bdet_inv_val hp, Pi.smul_apply]
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [(stab_entry hp hj).2, Pi.single_eq_of_ne hj, smul_zero]
  unfold TF.col
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]

theorem col_continuous (i₀ : ι) : Continuous fun κ : GL ι 𝔸[k] => TF.col i₀ κ := by
  unfold TF.col
  exact (Units.continuous_coe_inv).matrix_mulVec continuous_const

theorem col_one (i₀ : ι) : TF.col (k := k) i₀ 1 = Pi.single i₀ 1 := by
  unfold TF.col
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

theorem col_unitVec {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    UnitVec (fun j => (TF.col i₀ κ j).1) := by
  intro w
  have h := sum_norm_sq ((((adStd k).kGL ι).inv_mem hκ).2 w) i₀
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  exact congrArg (fun x : 𝔸[k] => ‖x.1 w‖ ^ 2) (col_apply i₀ κ j)

theorem col_prim {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    Prim fun j => (TF.col i₀ κ j).2 := by
  refine ⟨fun j => ?_, fun j => ((κ : Matrix ι ι 𝔸[k]) i₀ j).2, fun j => ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun x : 𝔸[k] => x.2 ∈ OH k) (col_apply i₀ κ j))
      (mem_OH_of_mem_intAd (hκ.1 j i₀).2)
  · exact mem_OH_of_mem_intAd (hκ.1 i₀ j).1
  · have h : ((κ : Matrix ι ι 𝔸[k]) * ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h
    have h2 := congrArg (finPart (k := k)) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h2
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
    rw [map_mul]
    exact congrArg (fun x : 𝔸[k] => finPart ((κ : Matrix ι ι 𝔸[k]) i₀ j) * finPart x) (col_apply i₀ κ j)

theorem bdet_split {p : GL ι 𝔸[k]} (hk : p ∈ (adStd k).kGL ι) {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ∃ (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ), bdet {i₀} p = ofInfinite a * ofFinite u ∧
      (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) ∧ u ∈ finiteIntegralUnits k := by
  refine ⟨toInfinite k (bdet {i₀} p), toFinite k (bdet {i₀} p), ?_, fun w => ?_, ?_⟩
  · rw [mul_comm, ofFinite_mul_ofInfinite]
  · have hv : ((toInfinite k (bdet {i₀} p) : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 := by
      rw [← bdet_val hp]; rfl
    rw [hv]
    have h := sum_norm_sq (hk.2 w) i₀
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
      rw [(stab_entry hp hj).1]
      show ‖(0 : w.Completion)‖ ^ 2 = 0
      simp)
      (fun h' => absurd (Finset.mem_univ _) h')] at h
    have h0 : 0 ≤ ‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ := norm_nonneg _
    nlinarith [h, h0, sq_nonneg (‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ - 1)]
  · rw [mem_finiteIntegralUnits]
    intro v
    have h1 : ((toFinite k (bdet {i₀} p) : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_val hp]; rfl
    have h2 : (((toFinite k (bdet {i₀} p))⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_inv_val hp, ← map_inv]; rfl
    rw [h1, h2]
    exact ⟨(mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).1)) v,
      (mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).2)) v⟩

theorem colLaw : ColLaw := by
  intro k _ _ ι _ _ i₀
  exact ⟨fun κ hκ => ⟨col_unitVec hκ i₀, col_prim hκ i₀⟩, col_continuous i₀, col_one i₀,
    fun p hk hp => ⟨col_mul hp, bdet_split hk hp⟩⟩

end GlobalTheory.CompanionTheory.EisCol
end
end
