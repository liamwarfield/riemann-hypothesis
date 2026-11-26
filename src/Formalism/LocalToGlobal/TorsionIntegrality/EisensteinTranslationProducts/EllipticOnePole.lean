module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
noncomputable section

namespace Formalism.L2.Th1.F

theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl

end Formalism.L2.Th1.F
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace OnePole

open AnalyticIdentityTheoremsZetaFacts

lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z := by
  exact tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const ω).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  simpa using hw

lemma eventually_notMem (L : PeriodPair) (p z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w - p ∉ L.lattice := by
  have hx : ∀ x : ℂ, ∀ᶠ u in 𝓝[≠] x, u ∉ L.lattice := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have hd : DiscreteTopology (L.lattice : Set ℂ) := (inferInstance : DiscreteTopology L.lattice)
      exact Filter.inf_principal_eq_bot.1 ((discreteTopology_subtype_iff.1 hd) x hx)
    · exact eventually_nhdsWithin_of_eventually_nhds ((L.isClosed_lattice.isOpen_compl).mem_nhds hx)
  have := (tendsto_add_nhdsNE z (-p)).eventually (hx (z + -p))
  simpa [sub_eq_add_neg] using this

lemma analyticAt_wZeta (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ (wZeta L) z := by
  exact (differentiableOn_wZeta L).analyticAt ((L.isClosed_lattice.isOpen_compl).mem_nhds hz)

lemma analyticAt_zetaExcept (L : PeriodPair) : AnalyticAt ℂ (zetaExcept L 0) 0 := by
  refine (differentiableOn_zetaExcept L 0).analyticAt ?_
  filter_upwards [eventually_nhdsWithin_iff.1 (eventually_notMem L 0 0)] with w hw
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe, not_and, not_not]
  intro hmem
  by_contra hne
  exact hw hne (by simpa using hmem)

lemma zeta_local (hq : ZetaQuasi) (L : PeriodPair) (p z₀ : ℂ) (h : z₀ - p ∈ L.lattice) :
    ∀ᶠ w in 𝓝[≠] z₀,
      wZeta L (w - p) = zetaExcept L 0 (w - z₀) + 1 / (w - z₀) + wEta L (z₀ - p) := by
  filter_upwards [eventually_notMem L z₀ z₀] with w hw
  rw [show w - p = w - z₀ + (z₀ - p) by ring, hq L (z₀ - p) (w - z₀) h hw, ← zetaExcept_zero_add]

lemma simple_local {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) (ho : -1 ≤ meromorphicOrderAt f p) :
    ∃ (r : ℂ) (k : ℂ → ℂ), AnalyticAt ℂ k p ∧ ∀ᶠ w in 𝓝[≠] p, f w = r / (w - p) + k w := by
  cases h : meromorphicOrderAt f p with
  | top =>
    refine ⟨0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h] with w hw
    simp [hw]
  | coe n =>
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
    have hn : (-1 : ℤ) ≤ n := by
      rw [h] at ho
      have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := by simpa using ho
      exact WithTop.coe_le_coe.1 h2
    rcases eq_or_lt_of_le hn with hn | hn
    · subst hn
      obtain ⟨q, hq⟩ := hg
      refine ⟨g p, dslope g p, ⟨_, hq.has_fpower_series_dslope_fslope⟩, ?_⟩
      filter_upwards [hfg, self_mem_nhdsWithin] with w hw hwp
      have hwp' : w ≠ p := hwp
      have hne : w - p ≠ 0 := sub_ne_zero.2 hwp'
      rw [hw, zpow_neg_one, smul_eq_mul, dslope_of_ne _ hwp', slope_def_field]
      field_simp
      ring
    · have hn0 : 0 ≤ n := by omega
      lift n to ℕ using hn0
      refine ⟨0, fun w => (w - p) ^ n * g w, by fun_prop, ?_⟩
      filter_upwards [hfg] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]

end OnePole

open OnePole AnalyticIdentityTheoremsZetaFacts

theorem ellipticOnePole_of (hN : EllipticNoPole) (hE : EllipticEntire) (hq : ZetaQuasi)
    (hL : Legendre) : EllipticOnePole := by
  intro L f p hmer hper hord hp
  obtain ⟨r, k, hk, hfk⟩ := simple_local (hmer p) hp
  set g : ℂ → ℂ := fun w => f w - r * wZeta L (w - p) with hg

  have hB : ∀ z, 0 ≤ meromorphicOrderAt f z →
      ∃ B : ℂ → ℂ, AnalyticAt ℂ B z ∧ f =ᶠ[𝓝[≠] z] B := by
    intro z hz
    cases h : meromorphicOrderAt f z with
    | top =>
      exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.1 h⟩
    | coe n =>
      obtain ⟨B, hBa, -, hfB⟩ := (meromorphicOrderAt_eq_int_iff (hmer z)).1 h
      have hn : 0 ≤ n := by rw [h] at hz; exact_mod_cast hz
      lift n to ℕ using hn
      refine ⟨fun w => (w - z) ^ n * B w, by fun_prop, ?_⟩
      filter_upwards [hfB] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]

  have hloc : ∀ z, ∃ A : ℂ → ℂ, AnalyticAt ℂ A z ∧ g =ᶠ[𝓝[≠] z] A := by
    intro z
    by_cases hz : z - p ∈ L.lattice
    · refine ⟨fun w => k (w - (z - p)) - r * zetaExcept L 0 (w - z) - r * wEta L (z - p), ?_, ?_⟩
      · have h1 : AnalyticAt ℂ (fun w => k (w - (z - p))) z := by
          have hk' : AnalyticAt ℂ k (z - (z - p)) := by simpa using hk
          exact AnalyticAt.comp (f := fun w : ℂ => w - (z - p)) (g := k) hk' (by fun_prop)
        have h2 : AnalyticAt ℂ (fun w => zetaExcept L 0 (w - z)) z := by
          have hz' : AnalyticAt ℂ (zetaExcept L 0) (z - z) := by simpa using analyticAt_zetaExcept L
          exact AnalyticAt.comp (f := fun w : ℂ => w - z) (g := zetaExcept L 0) hz' (by fun_prop)
        exact (h1.sub (analyticAt_const.mul h2)).sub analyticAt_const
      · have hshift : Tendsto (fun w : ℂ => w - (z - p)) (𝓝[≠] z) (𝓝[≠] p) := by
          have h' := tendsto_add_nhdsNE z (-(z - p))
          rw [show z + -(z - p) = p by ring] at h'
          simpa only [← sub_eq_add_neg] using h'
        filter_upwards [hshift.eventually hfk, zeta_local hq L p z hz] with w hw1 hw2
        have hfw : f w = f (w - (z - p)) := by
          have := hper (z - p) hz (w - (z - p))
          rw [sub_add_cancel] at this
          exact this
        show f w - r * wZeta L (w - p) = _
        rw [hfw, hw1, hw2, show w - (z - p) - p = w - z by ring]
        ring
    · obtain ⟨B, hBa, hfB⟩ := hB z (hord z hz)
      refine ⟨fun w => B w - r * wZeta L (w - p), ?_, ?_⟩
      · have : AnalyticAt ℂ (wZeta L) (z - p) := analyticAt_wZeta L _ hz
        exact hBa.sub (analyticAt_const.mul
          (AnalyticAt.comp (f := fun w : ℂ => w - p) (g := wZeta L) this (by fun_prop)))
      · filter_upwards [hfB] with w hw
        show f w - r * wZeta L (w - p) = _
        rw [hw]

  set G : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) g with hG
  have hGA : ∀ z, ∀ A : ℂ → ℂ, AnalyticAt ℂ A z → g =ᶠ[𝓝[≠] z] A → G =ᶠ[𝓝 z] A := by
    intro z A hA hgA
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ ({z}ᶜ : Set ℂ) → g y = A y := eventually_nhdsWithin_iff.1 hgA
    filter_upwards [eventually_eventually_nhds.2 h1, hA.eventually_analyticAt] with w hw hAw
    show limUnder (𝓝[≠] w) g = A w
    apply Tendsto.limUnder_eq
    by_cases hwz : w = z
    · subst hwz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgA.symm
    · have hgw : g =ᶠ[𝓝[≠] w] A := by
        apply eventually_nhdsWithin_of_eventually_nhds
        filter_upwards [hw, isOpen_ne.mem_nhds hwz] with y hy hyz
        exact hy hyz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgw.symm
  have hGd : Differentiable ℂ G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    exact hA.differentiableAt.congr_of_eventuallyEq (hGA z A hA hgA)
  have hgG : ∀ z, g =ᶠ[𝓝[≠] z] G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    filter_upwards [hgA, nhdsWithin_le_nhds (hGA z A hA hgA)] with w h1 h2
    rw [h1, h2]

  have hGq : ∀ ω ∈ L.lattice, ∀ w, G (w + ω) = G w - r * wEta L ω := by
    intro ω hω w
    refine eq_of_eventuallyEq_nhdsNE (g₁ := fun y => G (y + ω)) (g₂ := fun y => G y - r * wEta L ω)
      (hGd.continuous.comp (continuous_add_const ω)).continuousAt
      (hGd.continuous.sub continuous_const).continuousAt ?_
    filter_upwards [(tendsto_add_nhdsNE w ω).eventually (hgG (w + ω)), hgG w,
      eventually_notMem L p w] with y h1 h2 h3
    show G (y + ω) = G y - r * wEta L ω
    rw [← h1, ← h2]
    show f (y + ω) - r * wZeta L (y + ω - p) = f y - r * wZeta L (y - p) - r * wEta L ω
    rw [hper ω hω y, show y + ω - p = (y - p) + ω by ring, hq L ω (y - p) hω h3]
    ring

  have hDd : Differentiable ℂ (deriv G) := fun z => ((hGd.analyticAt z).deriv).differentiableAt
  have hDp : IsPeriodic L (deriv G) := by
    intro ω hω z
    have hfun : (fun y => G (y + ω)) = fun y => G y - r * wEta L ω := funext fun y => hGq ω hω y
    rw [← deriv_comp_add_const, hfun, deriv_sub_const]
  have hDc := hE L (deriv G) hDd hDp
  set a := deriv G 0 with ha
  have hlin : ∀ w, G w = a * w + G 0 := by
    have hH : Differentiable ℂ (fun w => G w - a * w) := hGd.sub (differentiable_id.const_mul a)
    have hH' : ∀ x, deriv (fun w => G w - a * w) x = 0 := by
      intro x
      have h1 : HasDerivAt G a x := by rw [← hDc x]; exact (hGd x).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => a * w) (a * 1) x := (hasDerivAt_id' x).const_mul a
      have h3 : HasDerivAt (fun w => G w - a * w) (a - a * 1) x := h1.sub h2
      rw [h3.deriv]
      ring
    intro w
    have := is_const_of_deriv_eq_zero hH hH' w 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this

  have hr : r = 0 := by
    have e1 := hGq L.ω₁ L.ω₁_mem_lattice 0
    have e2 := hGq L.ω₂ L.ω₂_mem_lattice 0
    rw [zero_add, hlin L.ω₁] at e1
    rw [zero_add, hlin L.ω₂] at e2
    have hs : (if 0 < (L.ω₂ / L.ω₁).im then (1 : ℂ) else -1) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · split_ifs <;> norm_num
      · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have key : r * (wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * e1 - L.ω₁ * e2
    rw [hL L] at key
    exact (mul_eq_zero.1 key).resolve_right hs

  have hGp : IsPeriodic L G := fun ω hω w => by rw [hGq ω hω w, hr]; ring
  refine ⟨G 0, fun z hz => ?_⟩
  have hfG : f =ᶠ[𝓝[≠] z] G := by
    filter_upwards [hgG z] with w hw
    rw [← hw]
    show f w = f w - r * wZeta L (w - p)
    rw [hr]
    ring
  rw [eq_of_eventuallyEq_nhdsNE hz (hGd z).continuousAt hfG]
  exact hE L G hGd hGp z

end Formalism.L2.Th1.F
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace ThreeTermRelation

lemma le_sub_of_add_le {o : WithTop ℤ} {m k : ℤ} (h : ((k + m : ℤ) : WithTop ℤ) ≤ o) :
    (k : WithTop ℤ) ≤ o - (m : WithTop ℤ) := by
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have := WithTop.coe_le_coe.1 h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_le_coe.2 (by omega)

lemma semiChar_mul_self (L : PeriodPair) (ω : ℂ) : semiChar L ω * semiChar L ω = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma eq_of_eventuallyEq_punctured {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (h : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma eventually_notMem (L : PeriodPair) (z : ℂ) : ∀ᶠ x in 𝓝[≠] z, x ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with x hx0 hx1
  have hx0' : x ≠ z := hx0
  simp_all

variable (L : PeriodPair) (b c : ℂ)

def threeTermDet (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
    - L.weierstrassP x * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + L.derivWeierstrassP x * (L.weierstrassP c - L.weierstrassP b)

def nAux (x : ℂ) : ℂ := threeTermDet L b c x * wSigma L x ^ 3

def threeTermDenom (x : ℂ) : ℂ := wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)

def threeTermQuotient (x : ℂ) : ℂ := nAux L b c x / threeTermDenom L b c x

def frobeniusStickelbergerDetMulSigmaCube (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
      * wSigma L x ^ 3
    - (x * dslope (wSigma L) 0 x ^ 3 + L.weierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + (-2 * dslope (wSigma L) 0 x ^ 3 + L.derivWeierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.weierstrassP c - L.weierstrassP b)

lemma sigma_zero (hz : SigmaZero) : wSigma L 0 = 0 := (hz L 0).2 (zero_mem _)

lemma analyticAt_dslope (he : SigmaEntire) : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := by
  obtain ⟨p, hp⟩ := (he L).analyticAt 0
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma wp_congr {x y : ℂ} (h : x + -y ∈ L.lattice) :
    L.weierstrassP x = L.weierstrassP y ∧ L.derivWeierstrassP x = L.derivWeierstrassP y := by
  have e : y + ((⟨x + -y, h⟩ : L.lattice) : ℂ) = x := by
    show y + (x + -y) = x
    ring
  have h1 := L.weierstrassP_add_coe y ⟨x + -y, h⟩
  have h2 := L.derivWeierstrassP_add_coe y ⟨x + -y, h⟩
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

lemma threeTermNum_eq_twistedGamma_of_sigmaZero (hz : SigmaZero) (x : ℂ) (hx : x ≠ 0) : nAux L b c x = frobeniusStickelbergerDetMulSigmaCube L b c x := by
  have hP := L.weierstrassPExcept_def 0 x
  have hP' := L.derivWeierstrassPExcept_def 0 x
  simp only [ZeroMemClass.coe_zero] at hP hP'
  unfold nAux threeTermDet frobeniusStickelbergerDetMulSigmaCube
  rw [hP, hP', dslope_of_ne _ hx, slope_def_field, sigma_zero L hz]
  field_simp
  ring

lemma twistedGamma_zero (hz : SigmaZero) (hs : SigmaSimple) :
    frobeniusStickelbergerDetMulSigmaCube L b c 0 = -2 * (L.weierstrassP c - L.weierstrassP b) := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_same, (hs L).1, sigma_zero L hz]
  ring

lemma twistedGamma_analyticAt_zero (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L b c) 0 := by
  have h3 := analyticAt_dslope L he
  have h4 : AnalyticAt ℂ (wSigma L) 0 := (he L).analyticAt 0
  have h5 := L.analyticAt_weierstrassPExcept 0
  have h6 := L.analyticAt_derivWeierstrassPExcept 0
  unfold frobeniusStickelbergerDetMulSigmaCube
  fun_prop

lemma sig_analyticAt (he : SigmaEntire) (β z : ℂ) : AnalyticAt ℂ (fun w => wSigma L (w + β)) z :=
  ((he L).comp (differentiable_id.add_const β)).analyticAt z

lemma sig_order_mem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∈ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((1 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp only [one_mul] at this
  rw [this, if_pos (by rwa [one_mul])]
  rfl

lemma sig_order_notMem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∉ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((0 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp only [one_mul] at this
  rw [this, if_neg (by rwa [one_mul])]
  rfl

lemma sig_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (β z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, wSigma L (x + β) ≠ 0 := by
  refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (sig_analyticAt L he β z).meromorphicAt).1 ?_
  by_cases h : z + β ∈ L.lattice
  · rw [sig_order_mem L hord h]; exact WithTop.coe_ne_top
  · rw [sig_order_notMem L hord h]; exact WithTop.coe_ne_top

lemma threeTermDenom_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, threeTermDenom L b c x ≠ 0 := by
  filter_upwards [sig_eventually_ne L he hord (b + c) z, sig_eventually_ne L he hord (-b) z,
    sig_eventually_ne L he hord (-c) z] with x h1 h2 h3
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

lemma threeTermDenom_analyticAt (he : SigmaEntire) (z : ℂ) : AnalyticAt ℂ (threeTermDenom L b c) z :=
  ((sig_analyticAt L he (b + c) z).mul (sig_analyticAt L he (-b) z)).mul
    (sig_analyticAt L he (-c) z)

lemma threeTermNum_analyticAt (he : SigmaEntire) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (nAux L b c) z := by
  have h4 : AnalyticAt ℂ (wSigma L) z := (he L).analyticAt z
  have h5 := L.analyticOnNhd_weierstrassP z hzL
  have h6 := L.analyticOnNhd_derivWeierstrassP z hzL
  unfold nAux threeTermDet
  fun_prop

lemma threeTermNum_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (nAux L b c) z := by
  have h4 : MeromorphicAt (wSigma L) z := ((he L).analyticAt z).meromorphicAt
  have h5 := L.meromorphic_weierstrassP z
  have h6 := L.meromorphic_derivWeierstrassP z
  unfold nAux threeTermDet
  fun_prop

lemma threeTermQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (threeTermQuotient L b c) z :=
  (threeTermNum_meromorphicAt L b c he z).div (threeTermDenom_analyticAt L b c he z).meromorphicAt

lemma threeTermQuotient_periodic (hq : SigmaQuasi) : IsPeriodic L (threeTermQuotient L b c) := by
  intro ω hω x
  have h0 := hq L ω x hω
  have h1 : wSigma L (x + ω + (b + c))
      = semiChar L ω * Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * wSigma L (x + (b + c)) := by
    rw [← hq L ω (x + (b + c)) hω]; congr 1; ring
  have h2 : wSigma L (x + ω + -b)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -b + ω / 2)) * wSigma L (x + -b) := by
    rw [← hq L ω (x + -b) hω]; congr 1; ring
  have h3 : wSigma L (x + ω + -c)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -c + ω / 2)) * wSigma L (x + -c) := by
    rw [← hq L ω (x + -c) hω]; congr 1; ring
  have hP : L.weierstrassP (x + ω) = L.weierstrassP x := L.weierstrassP_add_coe x ⟨ω, hω⟩
  have hP' : L.derivWeierstrassP (x + ω) = L.derivWeierstrassP x :=
    L.derivWeierstrassP_add_coe x ⟨ω, hω⟩
  have hE : Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * Complex.exp (wEta L ω * (x + -b + ω / 2))
        * Complex.exp (wEta L ω * (x + -c + ω / 2))
      = Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hχ : semiChar L ω ≠ 0 := fun h => by simpa [h] using semiChar_mul_self L ω
  have hne : semiChar L ω ^ 3 * Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hχ) (pow_ne_zero _ (Complex.exp_ne_zero _))
  unfold threeTermQuotient nAux threeTermDenom threeTermDet
  rw [h0, h1, h2, h3, hP, hP']
  rw [← mul_div_mul_left _ (wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)) hne]
  congr 1
  · ring
  · rw [← hE]; ring

lemma threeTermQuotient_order_ge (he : SigmaEntire) {z : ℂ} {k m1 m2 m3 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ))
    (h2 : meromorphicOrderAt (fun w => wSigma L (w + -b)) z = (m2 : WithTop ℤ))
    (h3 : meromorphicOrderAt (fun w => wSigma L (w + -c)) z = (m3 : WithTop ℤ))
    (hN : ((k + (m1 + m2 + m3) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (nAux L b c) z) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have hm : meromorphicOrderAt (threeTermDenom L b c) z = ((m1 + m2 + m3 : ℤ) : WithTop ℤ) := by
    have e : threeTermDenom L b c = ((fun w => wSigma L (w + (b + c))) * (fun w => wSigma L (w + -b)))
        * (fun w => wSigma L (w + -c)) := rfl
    rw [e, meromorphicOrderAt_mul ((sig_analyticAt L he (b + c) z).mul
        (sig_analyticAt L he (-b) z)).meromorphicAt (sig_analyticAt L he (-c) z).meromorphicAt,
      meromorphicOrderAt_mul (sig_analyticAt L he (b + c) z).meromorphicAt
        (sig_analyticAt L he (-b) z).meromorphicAt, h1, h2, h3]
    rfl
  unfold threeTermQuotient
  rw [fun_meromorphicOrderAt_div (threeTermNum_meromorphicAt L b c he z)
    (threeTermDenom_analyticAt L b c he z).meromorphicAt, hm]
  exact le_sub_of_add_le hN

lemma one_le_order {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z) (h0 : f z = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  rw [han.meromorphicOrderAt_eq]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1) han).mpr fun i hi ↦ ?_)
  interval_cases i
  simpa using h0

lemma threeTermNum_eq_zero_left {z : ℂ} (h : z + -b ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]; ring

lemma threeTermNum_eq_zero_right {z : ℂ} (h : z + -c ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]; ring

lemma threeTermQuotient_order_off (he : SigmaEntire) (hord : SigmaOrder) (hm : b - c ∉ L.lattice) {z : ℂ}
    (hzL : z ∉ L.lattice) {m1 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ)) :
    ((-m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have han := threeTermNum_analyticAt L b c he z hzL
  by_cases hb : z + -b ∈ L.lattice
  · have hc : z + -c ∉ L.lattice := fun hc => hm (by
      have := L.lattice.sub_mem hc hb
      convert this using 1; ring)
    refine threeTermQuotient_order_ge L b c he h1 (sig_order_mem L hord hb) (sig_order_notMem L hord hc) ?_
    have := one_le_order han (threeTermNum_eq_zero_left L b c hb)
    convert this using 2; ring
  · by_cases hc : z + -c ∈ L.lattice
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_mem L hord hc) ?_
      have := one_le_order han (threeTermNum_eq_zero_right L b c hc)
      convert this using 2; ring
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_notMem L hord hc) ?_
      have := han.meromorphicOrderAt_nonneg
      convert this using 1
      simp

lemma threeTermQuotient_order_zero (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (threeTermQuotient L b c) 0 := by
  have hN : 0 ≤ meromorphicOrderAt (nAux L b c) 0 := by
    have : nAux L b c =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L b c := by
      filter_upwards [self_mem_nhdsWithin] with x hx using threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx
    rw [meromorphicOrderAt_congr this]
    exact (twistedGamma_analyticAt_zero L b c he).meromorphicOrderAt_nonneg
  have := threeTermQuotient_order_ge L b c he (z := 0) (k := 0)
    (sig_order_notMem L hord (by simpa using hp))
    (sig_order_notMem L hord (by simpa using hb))
    (sig_order_notMem L hord (by simpa using hc)) (by simpa using hN)
  simpa using this

lemma threeTermQuotient_order_lattice (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder) (hq : SigmaQuasi)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) {z : ℂ}
    (hzL : z ∈ L.lattice) : 0 ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have h := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := 0) (c := z)
    (f := threeTermQuotient L b c)
  have h' : threeTermQuotient L b c ∘ (· + z) = threeTermQuotient L b c := funext fun x => threeTermQuotient_periodic L b c hq z hzL x
  rw [h', zero_add] at h
  rw [← h]
  exact threeTermQuotient_order_zero L b c he hz hord hb hc hp

lemma core (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice)
    (hm : b - c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨k, hk⟩ := h1 L (threeTermQuotient L b c) (-(b + c)) (threeTermQuotient_meromorphicAt L b c he)
    (threeTermQuotient_periodic L b c hq)
    (fun z hzp => by
      by_cases hzL : z ∈ L.lattice
      · exact threeTermQuotient_order_lattice L b c he hz hord hq hb hc hp hzL
      · have := threeTermQuotient_order_off L b c he hord hm hzL
          (sig_order_notMem L hord (β := b + c) (by rwa [sub_neg_eq_add] at hzp))
        simpa using this)
    (by
      have hpL : -(b + c) ∉ L.lattice := fun h => hp (by simpa using L.lattice.neg_mem h)
      have := threeTermQuotient_order_off L b c he hord hm hpL
        (sig_order_mem L hord (β := b + c) (by simp))
      simpa using this)
  have hev : ∀ z, ∀ᶠ x in 𝓝[≠] z, nAux L b c x = k * threeTermDenom L b c x := by
    intro z
    filter_upwards [eventually_notMem L z, threeTermDenom_eventually_ne L b c he hord z] with x hx1 hx2
    have := hk x ((threeTermNum_analyticAt L b c he x hx1).div (threeTermDenom_analyticAt L b c he x) hx2).continuousAt
    unfold threeTermQuotient at this
    rw [div_eq_iff hx2] at this
    exact this
  have hmc : ∀ z, ContinuousAt (fun x => k * threeTermDenom L b c x) z := fun z =>
    continuousAt_const.mul (threeTermDenom_analyticAt L b c he z).continuousAt
  have h0 : frobeniusStickelbergerDetMulSigmaCube L b c 0 = k * threeTermDenom L b c 0 := by
    refine eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (twistedGamma_analyticAt_zero L b c he).continuousAt (hmc 0) ?_
    filter_upwards [hev 0, self_mem_nhdsWithin] with x hx1 hx2
    rw [← threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx2, hx1]
  have ha' : nAux L b c a = k * threeTermDenom L b c a :=
    eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (threeTermNum_analyticAt L b c he a ha).continuousAt (hmc a) (hev a)
  have hS : wSigma L (b + c) ≠ 0 := fun h => hp ((hz L _).1 h)
  have h3 := hadd L b c hb hc
  rw [twistedGamma_zero L b c hz hs] at h0
  unfold threeTermDenom at h0 ha'
  unfold nAux at ha'
  rw [zero_add, zero_add, zero_add, ho L b, ho L c] at h0
  have e1 : a + (b + c) = a + b + c := by ring
  have e2 : a + -b = a - b := by ring
  have e3 : wSigma L (a + -c) = -wSigma L (c - a) := by rw [← ho L]; congr 1; ring
  rw [e1, e2, e3] at ha'
  refine mul_left_cancel₀ hS ?_
  linear_combination (wSigma L (b + c) * wSigma L b ^ 3 * wSigma L c ^ 3) * ha'
    + (wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a) * wSigma L b ^ 2 * wSigma L c ^ 2) * h0
    - (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a)) * h3

lemma trivial_case (hz : SigmaZero) {a : ℂ} (hm : b - c ∈ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨h1, h2⟩ := wp_congr L (x := b) (y := c) (by simpa [sub_eq_add_neg] using hm)
  rw [(hz L (b - c)).2 hm]
  unfold threeTermDet
  rw [h1, h2]; ring

lemma step (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  by_cases hm : b - c ∈ L.lattice
  · exact trivial_case L b c hz hm
  · exact core L b c h1 hord hq hz he ho hs hadd ha hb hc hp hm

lemma det_eq (a : ℂ) :
    Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                  1, L.weierstrassP b, L.derivWeierstrassP b;
                  1, L.weierstrassP c, L.derivWeierstrassP c] = threeTermDet L b c a := by
  rw [Matrix.det_fin_three]
  simp [threeTermDet]
  ring

lemma threeTermDet_cycle (a : ℂ) : threeTermDet L b c a = threeTermDet L c a b := by
  unfold threeTermDet; ring

end ThreeTermRelation

open ThreeTermRelation in
theorem sigmaThree_of (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) : SigmaThree := by
  intro L a b c ha hb hc
  rw [det_eq]
  by_cases hp1 : b + c ∈ L.lattice
  · by_cases hp2 : c + a ∈ L.lattice
    · have hm : a - b ∈ L.lattice := by
        have := L.lattice.sub_mem hp2 hp1
        convert this using 1; ring
      have := trivial_case L a b hz (a := c) hm
      rw [threeTermDet_cycle, threeTermDet_cycle]
      have e : c + a + b = a + b + c := by ring
      rw [e] at this
      linear_combination this
    · have := step L c a h1 hord hq hz he ho hs hadd hb hc ha hp2
      rw [threeTermDet_cycle]
      have e : b + c + a = a + b + c := by ring
      rw [e] at this
      linear_combination this
  · exact step L b c h1 hord hq hz he ho hs hadd ha hb hc hp1

theorem sgStarThree_of (h : SigmaThree) : SgStarThree := by
  intro L a b c ha hb hc
  have h0 := h L a b c ha hb hc
  have hexp : (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3
      = Complex.exp (-(s2 L) * (a + b + c) ^ 2 / 2) * Complex.exp (-(s2 L) * (a - b) ^ 2 / 2)
        * Complex.exp (-(s2 L) * (b - c) ^ 2 / 2) * Complex.exp (-(s2 L) * (c - a) ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  unfold sgStar
  generalize Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c] = D at h0 ⊢
  linear_combination (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3 * h0
    + (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a)) * hexp

open ThreeTermRelation in
theorem thetaLine_of (h1 : EllipticOnePole) (hq : SgStarQuasi) (hb : SgStarBasic) : ThetaLine := by
  intro L F hF hfe
  obtain ⟨hd, -, hzero, hder, -⟩ := hb L
  have hmer : ∀ z, MeromorphicAt (fun z => F z / sgStar L z) z := fun z =>
    (hF.analyticAt z).meromorphicAt.div (hd.analyticAt z).meromorphicAt
  have hper : IsPeriodic L (fun z => F z / sgStar L z) := by
    intro ω hω z
    have e1 := hfe ω hω z
    have e2 := hq L ω z hω
    have e3 := semiChar_mul_self L ω
    have hχ : (semiChar L ω)⁻¹ = semiChar L ω := inv_eq_of_mul_eq_one_left e3
    unfold opU at e1
    have hE : Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2)
        = (Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [hE] at e1
    show F (z + ω) / sgStar L (z + ω) = F z / sgStar L z
    rw [e2, ← e1, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, hχ]
    ring
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z => F z / sgStar L z) z := fun z hz =>
    (hF.analyticAt z).div (hd.analyticAt z) (fun h => hz ((hzero z).1 h))
  have hord0 : meromorphicOrderAt (sgStar L) 0 = 1 := by
    rw [(hd.analyticAt 0).meromorphicOrderAt_eq,
      (hd.analyticAt 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hzero 0).2 (zero_mem _))
        (by rw [hder]; exact one_ne_zero)]
    rfl
  obtain ⟨c, hc⟩ := h1 L (fun z => F z / sgStar L z) 0 hmer hper
    (fun z hz => (han z (by simpa using hz)).meromorphicOrderAt_nonneg) (by
      have hF0 := (hF.analyticAt 0).meromorphicOrderAt_nonneg
      rw [fun_meromorphicOrderAt_div (hF.analyticAt 0).meromorphicAt (hd.analyticAt 0).meromorphicAt,
        hord0]
      have := le_sub_of_add_le (o := meromorphicOrderAt F 0) (m := 1) (k := -1) (by simpa using hF0)
      simpa using this)
  have hoff : ∀ z, z ∉ L.lattice → F z = c * sgStar L z := by
    intro z hz
    have := hc z (han z hz).continuousAt
    have hne : sgStar L z ≠ 0 := fun h => hz ((hzero z).1 h)
    field_simp at this
    rw [this, mul_comm]
  refine ⟨c, fun z => ?_⟩
  refine eq_of_eventuallyEq_punctured (f := F) (g := fun z => c * sgStar L z)
    hF.continuous.continuousAt (continuous_const.mul hd.continuous).continuousAt ?_
  filter_upwards [eventually_notMem L z] with x hx using hoff x hx

end Formalism.L2.Th1.F
end
end

namespace Formalism.L2.Th1.F

theorem ellipticEntire : EllipticEntire := elliptic_entire_const
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
