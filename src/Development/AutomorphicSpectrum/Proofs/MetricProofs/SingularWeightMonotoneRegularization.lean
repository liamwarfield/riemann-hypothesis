module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace AnMono

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_isPosPot (A : FinHolAtlas e X) (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem log_inv_ge {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / t) ∧ 0 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  exact ⟨h1, Real.log_nonneg h1⟩

theorem quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_ge ht hte
  exact div_nonneg h2 (by linarith)

theorem epsT_mono {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    epsT C t ≤ epsT C' t := by
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (quot_nonneg ht hte)

theorem mul_epsT_mono {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    C * epsT C t ≤ C' * epsT C' t := by
  have hx := quot_nonneg ht hte
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem exp_one_le_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hs y
  unfold rW
  linarith

theorem one_le_log_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    1 ≤ Real.log (rW L s y) := by
  have := Real.log_le_log (Real.exp_pos 1) (exp_one_le_rW L s hs y)
  rwa [Real.log_exp] at this

theorem isSingWeight_mono (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X) (ph : X → ℝ) {C₅ C₅' : ℝ} (hC : C₅ ≤ C₅')
    (h : IsSingWeight A L s th ph C₅) : IsSingWeight A L s th ph C₅' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨h5, h6⟩ := h4 y hy
  have hl := one_le_log_rW L s hs y
  constructor
  · nlinarith
  · linarith

theorem isRegFamily_enlarge (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) {C t₀ C' t₁ : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hs : ∀ y, logNormSec L s y ≤ 0)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀)
    (hte : t₁ ≤ Real.exp (-1)) : IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y =>
    (Real.exp_pos 1).le.trans (exp_one_le_rW L s hs y)
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-1) := htt.trans hte
  have hε := epsT_mono hCC ht hte'
  have hll := (log_inv_ge ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_,
    fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_mono hC (ht.trans_le htt') (ht'.trans hte)
    linarith

theorem continuous_of_smooth (A : FinHolAtlas e X) (u : X → ℝ) (h : A.Smooth u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (u ∘ (A.chart j).symm) (A.chart j).target := by
    have := (h j).continuousOn
    simpa using this
  have hx : (A.chart j) x ∈ (A.chart j).target := (A.chart j).map_source hj
  have h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    h1.continuousAt ((A.chart j).open_target.mem_nhds hx)
  have h3 : ContinuousAt (A.chart j) x := (A.chart j).continuousAt hj
  have h4 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (g := u ∘ (A.chart j).symm) h2 h3
  refine h4.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendstoUniformlyOn_self {α β : Type*} [UniformSpace β] (f : α → β) (p : Filter ℝ)
    (K : Set α) : TendstoUniformlyOn (fun _ : ℝ => f) f p K := by
  intro v hv
  exact Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hv

theorem isRegFamilyC2_const (A : FinHolAtlas e X) (s : X → X → ℂ) (u : X → ℝ) :
    IsRegFamilyC2 A s u (fun _ => u) := fun j K _ _ =>
  ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _⟩

theorem isPsh_add_rsmul (A : FinHolAtlas e X) (Θ th : LocPot X) (u : X → ℝ) {ε : ℝ}
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th) (hu : A.Smooth u)
    (hε : 0 ≤ ε) (h : IsPsh A (th + LocPot.ofFun u)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε) := by
  refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th u hΘ hΘp hth hu hε ?_
  intro x j y hy w
  have hfun : (th + LocPot.ofFun u + Θ.rsmul 0).φ x ∘ (A.chart j).symm =
      (th + LocPot.ofFun u).φ x ∘ (A.chart j).symm := by
    funext z
    show th.φ x _ + u _ + 0 * Θ.φ x _ = th.φ x _ + u _
    ring
  rw [hfun]
  exact h x j y ⟨hy.1, hy.2.1⟩ w

theorem smooth_member [CompactSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ)
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X)
    (u : X → ℝ) (hth : IsPotential A th) (hu : A.Smooth u) (hp : IsPsh A (th + LocPot.ofFun u)) :
    ∃ C₀, IsSingWeight A L s th u C₀ ∧
      IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
        IsRegFamilyC2 A s u (fun _ => u) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_smooth A u hu).continuousOn
  have hb : ∀ y, |u y| ≤ |M| + 1 := fun y => by
    have := hM y (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M]
  set C₀ : ℝ := |M| + 1 with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀, ⟨hth, fun j => (hu j).mono ?_, fun x j y hy w => ?_, fun y _ => ?_⟩, ?_,
    isRegFamilyC2_const A s u⟩
  · exact fun z hz => ⟨hz.1, Set.mem_univ _⟩
  · exact hp x j y ⟨hy.1, hy.2.1⟩ w
  · have hl := one_le_log_rW L s hs y
    have h := abs_le.1 (hb y)
    constructor
    · nlinarith
    · exact h.2
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    refine ⟨Real.exp_pos _, ?_, fun t ht htt => ?_⟩
    · exact Real.exp_lt_one_iff.2 (by linarith)
    have hl := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht htt
    have hq := GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg ht htt
    have hε : 0 ≤ epsT C₀ t := by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 hq
    have hε' : ∀ t', 0 < t' → t' ≤ Real.exp (-Real.exp 1) → 0 ≤ C₀ * epsT C₀ t' := fun t' h0 h1 => by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 (mul_nonneg hC0 (GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg h0 h1))
    have h3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨hu, fun y => (abs_le.1 (hb y)).2, fun y _ => le_rfl, fun y => ?_,
      isPsh_add_rsmul A Θ th u hΘ hΘp hth hu hε hp, fun y _ _ => by linarith, fun y _ => ?_,
      fun t' htt' ht' y => ?_⟩
    · have h := abs_le.1 (hb y)
      nlinarith [hl.2]
    · have := mul_nonneg hε (he.le.trans (exp_one_le_rW L s hs y))
      linarith
    · have := hε' t' (ht.trans_le htt') ht'
      linarith

end AnMono

theorem enlarging_constants_smooth_members :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
      (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
      IsPotential A Θ → IsPosPot A Θ →
      (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧
      (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
        IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th →
        IsRegFamily A Θ L s th ph phT C' t₀') ∧
      ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) →
        ∃ C₀, IsSingWeight A L s th u C₀ ∧
          IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
            IsRegFamilyC2 A s u (fun _ => u) := by
  intro e X _ _ _ A Θ L s nb m W _ _ _ hs hΘ hΘpos
  have hΘp := AnMono.isPsh_of_isPosPot A Θ hΘpos
  refine ⟨fun th ph C₅ C₅' hC h => AnMono.isSingWeight_mono A L s hs th ph hC h,
    fun th ph phT C t₀ C' t₀' hC h0 h1 h2 hF hth => ?_,
    fun th u hth hu hp => AnMono.smooth_member A Θ L s hΘ hΘp hs th u hth hu hp⟩
  exact AnMono.isRegFamily_enlarge A Θ L s th ph phT hΘ hΘp hth hs hF hC h0 h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularizationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_weight_monotone_regularization : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧ (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) → IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th → IsRegFamily A Θ L s th ph phT C' t₀') ∧ ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) → ∃ C₀, IsSingWeight A L s th u C₀ ∧ IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧ IsRegFamilyC2 A s u (fun _ => u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | exact GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunction
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IDefect
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace IDef

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def wt : (Σ k, ι k) → K → ℤ := fun p => Pi.single p.1 1

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt (ι := ι)) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro b _ hb
    simp [wt, Pi.single_eq_of_ne hb.symm]
  · simp

theorem mem_of_homog {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (fun k => (a k : ℤ)) := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  funext k
  rw [weight_wt, h d (mem_support_iff.mpr hd) k]

theorem evC_smul {s : MRing ι} {d : K → ℤ} (h : s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : evC (fun p => c p.1 * z p) s = (∏ k, c k ^ d k) * evC z s := by
  rw [mem_weightedHomogeneousSubmodule] at h
  by_cases hs : s = 0
  · simp [hs, evC]
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.mp hs
  have h1 : ∀ k, d k = ((∑ i, m₀ ⟨k, i⟩ : ℕ) : ℤ) := fun k => by rw [← h hm₀, weight_wt]
  have h2 : IsMultiHomog s fun k => ∑ i, m₀ ⟨k, i⟩ := by
    intro m hm k
    have := weight_wt m k
    rw [h (mem_support_iff.mp hm), h1] at this
    exact_mod_cast this.symm
  simp only [h1, zpow_natCast]
  exact eval_smul_homog s _ h2 c z

theorem homog_ideal {P : Ideal (MRing ι)} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨_, mem_of_homog ha⟩

theorem exists_homog_pair {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {f g u v : MRing ι} {α γ : K → ℕ}
    (hf : IsMultiHomog f α) (hg : IsMultiHomog g γ) (h : u * f - v * g ∈ P) {z : (Σ k, ι k) → ℂ}
    (hu : evC z u ≠ 0) : ∃ (u' v' : MRing ι) (d : K → ℤ), u' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d ∧
      v' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) ∧
      u' * f - v' * g ∈ P ∧ evC z u' ≠ 0 := by
  classical
  set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι)) with h𝒜
  have h1 : ∃ d, evC z (DirectSum.decompose 𝒜 u d : MRing ι) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    rw [← DirectSum.sum_support_decompose 𝒜 u]
    unfold evC at hc ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun d _ => hc d
  obtain ⟨d, hd⟩ := h1
  refine ⟨_, _, d, (DirectSum.decompose 𝒜 u d).2,
    (DirectSum.decompose 𝒜 v (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ))).2, ?_, hd⟩
  have h2 := homog_ideal hP (d + fun k => (α k : ℤ)) h
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hf),
    ← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hg), sub_add_cancel]
  rw [DirectSum.decompose_sub] at h2
  exact h2

omit [DecidableEq K] in
theorem exists_pair {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, evC z u ≠ 0 ∧ evC z v ≠ 0 ∧ u * f - v * g ∈ P := by
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  exact h.2.2 (RingHom.ker φ) (RingHom.ker_isPrime φ) (fun s hs => hz.2 s hs) fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa [φ, RingHom.mem_ker] using hi⟩

omit [DecidableEq K] in
theorem ratio_eq {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g u v u' v' : MRing ι} (hg : g ∉ P)
    (h : u * f - v * g ∈ P) (h' : u' * f - v' * g ∈ P) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hu : evC z u ≠ 0) (hu' : evC z u' ≠ 0) : ‖evC z v‖ / ‖evC z u‖ = ‖evC z v'‖ / ‖evC z u'‖ := by
  have h1 : (u * v' - u' * v) * g ∈ P := by
    have := P.sub_mem (P.mul_mem_left u' h) (P.mul_mem_left u h')
    convert this using 1
    ring
  have h2 := hz.2 _ ((hP.mem_or_mem h1).resolve_right hg)
  rw [← norm_div, ← norm_div]
  congr 1
  unfold evC at *
  simp only [map_sub, map_mul] at h2
  field_simp
  linear_combination -h2

end IDef

open IDef HolomorphicMinorCharts in
theorem i_defect : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) := by
  intro K _ ι _ P J e R A B f g hP hI hA hB
  classical
  obtain ⟨⟨α, γ, hf, hg, hdeg⟩, hU⟩ := hI
  let w : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 then
      Real.log (‖evC z h.choose.2‖ / ‖evC z h.choose.1‖ * B.h z / A.h z) else 0
  have hw : IsDefectOn P (mcPts P) f g A B w := by
    intro z hz u v h hu
    have hex : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 := ⟨(u, v), h, hu⟩
    simp only [w, dif_pos hex]
    rw [ratio_eq hP.1 hU.2.1 hex.choose_spec.1 h hz hex.choose_spec.2 hu]
  have hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z' := by
    intro z hz z' hzz
    have hz' : z' ∈ mcPts P := mem_mcPts_of_sameOrbit hP.2.1 (so_symm hzz) hz
    obtain ⟨u₀, v₀, hu₀, -, h₀⟩ := exists_pair hU hz'
    obtain ⟨u, v, d, hu, hv, h, hu'⟩ := exists_homog_pair hP.2.1 hf hg h₀ hu₀
    obtain ⟨c, hc, rfl⟩ := hzz
    have hn : ∀ n : K → ℤ, (∏ k, c k ^ n k) ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hn' : ∀ n : K → ℤ, (∏ k, ‖c k‖ ^ n k) ≠ 0 := fun n =>
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [hw _ hz u v h (by rw [evC_smul hu]; exact mul_ne_zero (hn d) hu'), hw _ hz' u v h hu', evC_smul hu, evC_smul hv,
      A.smul c z' hc, B.smul c z' hc]
    congr 1
    simp only [norm_mul, norm_prod, norm_zpow]
    have key : (∏ k, ‖c k‖ ^ (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) k) * ∏ k, ‖c k‖ ^ B.a k =
        (∏ k, ‖c k‖ ^ d k) * ∏ k, ‖c k‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (norm_ne_zero_iff.mpr (hc k)), ← zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
      congr 1
      have := hdeg k
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    have h1 := hn' d
    have h2 := hn' A.a
    have h3 := (A.pos z' hz'.1).ne'
    have h4 := norm_ne_zero_iff.mpr hu'
    field_simp
    linear_combination ‖evC z' v‖ * B.h z' * key
  refine ⟨w, hw, hinv, fun j y hy => ContDiffAt.contDiffWithinAt ?_⟩
  set x := (R.A.chart j).symm y with hx
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds ⟨hy.1, R.mem_U x⟩
  have hz := R.mem x x (R.mem_U x)
  obtain ⟨u, v, hu, hv, h⟩ := exists_pair hU hz
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => R.lift x ((R.A.chart j).symm y)) y :=
    (contDiffOn_lift R x j).contDiffAt hO
  have hev : ∀ s : MRing ι, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => evC (R.lift x ((R.A.chart j).symm y)) s) y := fun s =>
    ContDiffAt.comp (g := fun z => evC z s) y
      (((AnalyticOnNhd.eval_mvPolynomial (map (Int.castRingHom ℂ) s)) _ trivial).contDiffAt.restrict_scalars ℝ) hl
  have hNZ : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun k => ?_
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ∀ C : HermLine ι, IsSmoothHerm C → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => C.h (R.lift x ((R.A.chart j).symm y))) y := fun C hC =>
    ContDiffAt.comp (g := C.h) y (ContDiffOn.contDiffAt hC (hNZ.mem_nhds hz.1)) hl
  have hA0 := (A.pos _ hz.1).ne'
  have hB0 := (B.pos _ hz.1).ne'
  have hu0 := norm_ne_zero_iff.mpr hu
  have hv0 := norm_ne_zero_iff.mpr hv
  refine ContDiffAt.congr_of_eventuallyEq
    ((((((hev v).norm ℂ hv).div ((hev u).norm ℂ hu) hu0).mul (hh B hB)).div (hh A hA) hA0).log
      (div_ne_zero (mul_ne_zero (div_ne_zero hv0 hu0) hB0) hA0)) ?_
  filter_upwards [hO, (hev u).continuousAt.eventually_ne hu] with y' h1 h2
  simp only [Function.comp_apply]
  rw [hinv _ (R.mem _ _ (R.mem_U _)) _ (R.compat _ x _ ⟨R.mem_U _, h1.2⟩)]
  exact hw _ (R.mem x _ h1.2) u v h h2

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunction
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem defect_exists_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) :=
  @PositivityTheory.UnitarySelfGeneration.i_defect

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunctionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_isomorphism_defect_function : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth | exact GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth <;> assumption)
end
end
