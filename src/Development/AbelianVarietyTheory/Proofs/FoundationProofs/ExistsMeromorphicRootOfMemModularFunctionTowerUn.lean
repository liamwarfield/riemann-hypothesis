module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section
namespace GlobalTheory.RootHs
open Metric Complex

lemma mem_ball_big (u : ℂ) (R ε : ℝ) (hε : 0 < ε) (hu : 2 * ε ≤ u.im) (hR : u.re ^ 2 + u.im ^ 2 < R * u.im)
    (hRε : ε < R) : u ∈ ball ((R : ℂ) * I) (R - ε) := by
  have hRe : 0 ≤ R - ε := by linarith
  rw [Metric.mem_ball, Complex.dist_eq]
  have hsq : ‖u - (R : ℂ) * I‖ ^ 2 = u.re ^ 2 + (u.im - R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hlt : ‖u - (R : ℂ) * I‖ ^ 2 < (R - ε) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R) (by linarith : (0:ℝ) ≤ u.im - 2 * ε), sq_nonneg ε]
  nlinarith [norm_nonneg (u - (R : ℂ) * I)]

lemma closedBall_big_sub (R ε : ℝ) (hε : 0 < ε) : closedBall ((R : ℂ) * I) (R - ε) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h1 := Complex.abs_im_le_norm (z - (R : ℂ) * I)
  have h2 : (z - (R : ℂ) * I).im = z.im - R := by simp
  rw [h2] at h1
  show 0 < z.im
  have h3 := neg_abs_le (z.im - R)
  linarith

lemma exists_disc (z₀ z : ℂ) (h₀ : 0 < z₀.im) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), closedBall c r ⊆ Hs ∧ z₀ ∈ ball c r ∧ z ∈ ball c r := by
  set ε : ℝ := min z₀.im z.im / 2 with hεdef
  have hε : 0 < ε := half_pos (lt_min h₀ hz)
  have h2ε₀ : 2 * ε ≤ z₀.im := by rw [hεdef]; linarith [min_le_left z₀.im z.im]
  have h2ε : 2 * ε ≤ z.im := by rw [hεdef]; linarith [min_le_right z₀.im z.im]
  have ha : 0 ≤ (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im := div_nonneg (by positivity) h₀.le
  have hb : 0 ≤ (z.re ^ 2 + z.im ^ 2) / z.im := div_nonneg (by positivity) hz.le
  set R : ℝ := (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im + (z.re ^ 2 + z.im ^ 2) / z.im + ε + 1 with hRdef
  have hR₀ : z₀.re ^ 2 + z₀.im ^ 2 < R * z₀.im := (div_lt_iff₀ h₀).mp (by rw [hRdef]; linarith)
  have hR : z.re ^ 2 + z.im ^ 2 < R * z.im := (div_lt_iff₀ hz).mp (by rw [hRdef]; linarith)
  have hRε : ε < R := by rw [hRdef]; linarith
  exact ⟨(R : ℂ) * I, R - ε, closedBall_big_sub R ε hε, mem_ball_big z₀ R ε hε h2ε₀ hR₀ hRε,
    mem_ball_big z R ε hε h2ε hR hRε⟩

theorem discRoot : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    (∃ z₀ ∈ Hs, h z₀ ≠ 0) → ∀ (c : ℂ) (r : ℝ), Metric.closedBall c r ⊆ Hs →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧ ∀ z ∈ Metric.ball c r, g z ^ m = h z := by
  rintro h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz => ?_⟩
    rw [Metric.ball_eq_empty.mpr hr] at hz
    exact absurd hz (Set.notMem_empty z)
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hHsConn : IsPreconnected Hs := by
    show IsPreconnected {z : ℂ | 0 < z.im}
    exact (convex_halfSpace_im_gt (r := 0)).isPreconnected
  have han : AnalyticOnNhd ℂ h Hs := hh.analyticOnNhd hHsOpen
  refine GlobalTheory.KZ.RootDisc.exists_root_disc h m c r hm hr (han.mono hsub) ?_
  intro τ hτ
  have hτ' := hsub hτ
  have hfin : analyticOrderAt h τ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHsConn hτ' htop hz₀)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmer : meromorphicOrderAt h τ = ((n : ℤ) : WithTop ℤ) := by
    rw [(han τ hτ').meromorphicOrderAt_eq, ← hn]
    rfl
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.mp (hdiv τ hτ' n hmer)
  exact ⟨k, by rw [← hn, hk]⟩

theorem rootUnique : ∀ (U : Set ℂ) (g₁ g₂ : ℂ → ℂ) (m : ℕ) (z₀ : ℂ), 0 < m → IsOpen U → IsPreconnected U →
    DifferentiableOn ℂ g₁ U → DifferentiableOn ℂ g₂ U → (∀ z ∈ U, g₁ z ^ m = g₂ z ^ m) → z₀ ∈ U →
    g₁ z₀ = g₂ z₀ → g₁ z₀ ≠ 0 → Set.EqOn g₁ g₂ U := by
  intro U g₁ g₂ m z₀ hm hU hC hg₁ hg₂ hpow hz₀ heq hne
  have hc₁ : ContinuousAt g₁ z₀ := (hg₁.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hc₂ : ContinuousAt g₂ z₀ := (hg₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hq : ContinuousAt (fun z => g₂ z / g₁ z) z₀ := hc₂.div hc₁ hne
  have hq0 : g₂ z₀ / g₁ z₀ = 1 := by rw [← heq, div_self hne]
  set S : Finset ℂ := (Polynomial.nthRoots m (1 : ℂ)).toFinset.erase 1 with hSdef
  have hS : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  have hopen : (S : Set ℂ)ᶜ ∈ 𝓝 (g₂ z₀ / g₁ z₀) := by
    rw [hq0]
    exact hS.isOpen_compl.mem_nhds (by simp [hSdef])
  have hev : g₁ =ᶠ[𝓝 z₀] g₂ := by
    filter_upwards [hq.preimage_mem_nhds hopen, hc₁.eventually_ne hne, hU.mem_nhds hz₀] with z hzS hz1 hzU
    have hroot : g₂ z / g₁ z ∈ Polynomial.nthRoots m (1 : ℂ) := by
      rw [Polynomial.mem_nthRoots hm, div_pow, ← hpow z hzU, div_self (pow_ne_zero _ hz1)]
    have h1 : g₂ z / g₁ z = 1 := by
      by_contra hne1
      exact hzS (Finset.mem_erase.mpr ⟨hne1, Multiset.mem_toFinset.mpr hroot⟩)
    rw [div_eq_one_iff_eq hz1] at h1
    exact h1.symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hg₁.analyticOnNhd hU) (hg₂.analyticOnNhd hU) hC hz₀ hev

theorem rootHs : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  classical
  intro h m hm hh hdiv
  by_cases hz : ∃ z₀ ∈ Hs, h z₀ ≠ 0
  swap
  · simp only [not_exists, not_and, not_not] at hz
    refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz' => ?_⟩
    rw [hz z hz', zero_pow hm.ne']
  obtain ⟨z₀, hz₀, hne⟩ := hz
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hm
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hw₀, zero_pow hm.ne'])
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have key : ∀ z ∈ Hs, ∃ (c : ℂ) (r : ℝ), z₀ ∈ ball c r ∧ z ∈ ball c r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball c r) ∧ (∀ y ∈ ball c r, g y ^ m = h y) ∧ g z₀ = w₀ := by
    intro z hz
    obtain ⟨c, r, hsub, h0, h1⟩ := exists_disc z₀ z hz₀ hz
    obtain ⟨g, hgd, hgp⟩ := discRoot h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
    have hg0 : g z₀ ≠ 0 := by
      intro h0'
      apply hne
      rw [← hgp z₀ h0, h0', zero_pow hm.ne']
    refine ⟨c, r, h0, h1, fun y => (w₀ / g z₀) * g y, hgd.const_mul _, fun y hy => ?_, ?_⟩
    · rw [mul_pow, div_pow, hgp y hy, hw₀, hgp z₀ h0, div_self hne, one_mul]
    · exact div_mul_cancel₀ w₀ hg0
  choose c r h0 h1 g hgd hgp hgz using key
  have hloc : ∀ z₁ (hz₁ : z₁ ∈ Hs) z (hz : z ∈ Hs), z ∈ ball (c z₁ hz₁) (r z₁ hz₁) →
      g z hz z = g z₁ hz₁ z := by
    intro z₁ hz₁ z hz hzb
    have hU : IsOpen (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) := isOpen_ball.inter isOpen_ball
    have hC : IsPreconnected (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    refine rootUnique _ (g z hz) (g z₁ hz₁) m z₀ hm hU hC ((hgd z hz).mono Set.inter_subset_left)
      ((hgd z₁ hz₁).mono Set.inter_subset_right) (fun y hy => by rw [hgp z hz y hy.1, hgp z₁ hz₁ y hy.2])
      ⟨h0 z hz, h0 z₁ hz₁⟩ ((hgz z hz).trans (hgz z₁ hz₁).symm) (by rw [hgz z hz]; exact hw₀ne) ⟨h1 z hz, hzb⟩
  refine ⟨fun z => if h' : z ∈ Hs then g z h' z else 0, ?_, ?_⟩
  · intro z₁ hz₁
    have hev : (fun z => if h' : z ∈ Hs then g z h' z else 0) =ᶠ[𝓝 z₁] g z₁ hz₁ := by
      have hmem : ball (c z₁ hz₁) (r z₁ hz₁) ∩ Hs ∈ 𝓝 z₁ := (isOpen_ball.inter hHsOpen).mem_nhds ⟨h1 z₁ hz₁, hz₁⟩
      filter_upwards [hmem] with z hz
      show (if h' : z ∈ Hs then g z h' z else 0) = g z₁ hz₁ z
      rw [dite_eq_left hz.2]
      exact hloc z₁ hz₁ z hz.2 hz.1
    exact (((hgd z₁ hz₁).differentiableAt (isOpen_ball.mem_nhds (h1 z₁ hz₁))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    show (if h' : z ∈ Hs then g z h' z else 0) ^ m = h z
    rw [dite_eq_left hz]
    exact hgp z hz z (h1 z hz)

end GlobalTheory.RootHs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvdStatement
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  first | exact @GlobalTheory.RootHs.rootHs | exact GlobalTheory.RootHs.rootHs | (intros; apply GlobalTheory.RootHs.rootHs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.ValAt

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_germ_eq {τ : ℂ} (hτ : τ ∈ Hs) {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  rw [Filter.Germ.coe_eq] at h
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz hz'
  rcases hz with hz | hz
  · exact hz
  · exact absurd hz' hz

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem _root_.GlobalTheory.KZ.ValAt.exists_rep (g : _root_.GlobalTheory.KZ.Mero) :
    ∃ φ : ℂ → ℂ, g = (φ : _root_.GlobalTheory.KZ.Mero) := by
  obtain ⟨φ, hφ⟩ := Quot.exists_rep g
  exact ⟨φ, hφ.symm⟩

def rep (X : Tower Ω ε) (x : X.K) : ℂ → ℂ := (exists_rep (X.an x)).choose

theorem rep_spec (X : Tower Ω ε) (x : X.K) : X.an x = (rep X x : Mero) := (exists_rep (X.an x)).choose_spec

def ord (X : Tower Ω ε) (τ : ℂ) (x : X.K) : WithTop ℤ := meromorphicOrderAt (rep X x) τ

theorem ord_eq (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) {x : X.K} {φ : ℂ → ℂ} (h : X.an x = (φ : Mero)) :
    ord X τ x = meromorphicOrderAt φ τ :=
  meromorphicOrderAt_congr (nhdsNE_of_germ_eq hτ ((rep_spec X x).symm.trans h))

private theorem an_eq_germ_rep (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) :
    X.an x = (_root_.GlobalTheory.KZ.ValAt.rep X x : _root_.GlobalTheory.KZ.Mero) :=
  (_root_.GlobalTheory.KZ.ValAt.exists_rep (X.an x)).choose_spec

private theorem isOpen_upperHalfPlaneSet' : IsOpen _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact isOpen_lt continuous_const Complex.continuous_im

private theorem eventuallyEq_nhdsNE_of_mero_coe_eq {φ ψ : ℂ → ℂ}
    (h : (φ : _root_.GlobalTheory.KZ.Mero) = ψ) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  have h' := (Filter.Germ.coe_eq.1 h : φ =ᶠ[codiscreteWithin _root_.GlobalTheory.KZ.Hs] ψ)
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at h'
  have hd := h' τ hτ
  rw [Filter.disjoint_principal_right] at hd
  filter_upwards [hd, nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet'.mem_nhds hτ)] with z h1 h2
  by_contra hne
  exact h1 ⟨h2, hne⟩

private theorem ord_eq_meromorphicOrderAt_of_an_eq_coe {φ : ℂ → ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) (h : X.an x = (φ : _root_.GlobalTheory.KZ.Mero)) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x = meromorphicOrderAt φ τ := by
  unfold _root_.GlobalTheory.KZ.ValAt.ord
  rw [an_eq_germ_rep] at h
  exact meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_mero_coe_eq h hτ)

private theorem isPreconnected_upperHalfPlaneSet : IsPreconnected _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact (convex_halfSpace_im_gt 0).isPreconnected

private theorem eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero {b : ℂ → ℂ}
    (hb : DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs)
    (hb0 : (b : _root_.GlobalTheory.KZ.Mero) ≠ 0) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
  have ha := hb.analyticOnNhd isOpen_upperHalfPlaneSet'
  rcases (ha τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    apply hb0
    have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_upperHalfPlaneSet hτ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    exact Filter.eventually_of_mem (self_mem_codiscreteWithin _) hz
  · exact h

private theorem exists_differentiableOn_rep_eventuallyEq_div (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a _root_.GlobalTheory.KZ.Hs ∧
      DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs ∧
      _root_.GlobalTheory.KZ.ValAt.rep X x =ᶠ[𝓝[≠] τ] a / b := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  refine ⟨a, b, ha, hb, ?_⟩
  rw [an_eq_germ_rep, ← Filter.Germ.coe_mul] at hab
  filter_upwards [eventuallyEq_nhdsNE_of_mero_coe_eq hab hτ, eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero hb hb0 hτ]
    with z h1 h2
  rw [Pi.div_apply, eq_div_iff h2]
  exact h1

private theorem meromorphicAt_rep_of_mem_upperHalfPlaneSet (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    MeromorphicAt (_root_.GlobalTheory.KZ.ValAt.rep X x) τ := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_differentiableOn_rep_eventuallyEq_div X x hτ
  have ha' := (ha.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  have hb' := (hb.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  exact (ha'.div hb').congr h.symm

theorem _root_.GlobalTheory.KZ.ValAt.ord_mul (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ (x * y) =
      _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ y := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x * y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x * _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_mul (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_mul, Filter.Germ.coe_mul, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

theorem _root_.GlobalTheory.KZ.ValAt.ord_add (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    min (_root_.GlobalTheory.KZ.ValAt.ord X τ x) (_root_.GlobalTheory.KZ.ValAt.ord X τ y) ≤
      _root_.GlobalTheory.KZ.ValAt.ord X τ (x + y) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x + y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x + _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_add (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_add (f := _), Filter.Germ.coe_add, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

theorem _root_.GlobalTheory.KZ.ValAt.ord_const (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (c : Ω) :
    0 ≤ _root_.GlobalTheory.KZ.ValAt.ord X τ (algebraMap Ω X.K c) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X _ (X.an_c c) hτ]
  exact analyticAt_const.meromorphicOrderAt_nonneg

theorem _root_.GlobalTheory.KZ.ValAt.ord_one (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : _root_.GlobalTheory.KZ.ValAt.ord X τ 1 = 0 := by
  classical
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X 1 (φ := fun _ => 1) (by rw [map_one]; rfl) hτ,
    meromorphicOrderAt_const]
  simp

theorem _root_.GlobalTheory.KZ.ValAt.ord_add_ord_inv (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) {x : X.K} (hx : x ≠ 0) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ x⁻¹ = 0 := by
  rw [← _root_.GlobalTheory.KZ.ValAt.ord_mul X hτ, mul_inv_cancel₀ hx,
    _root_.GlobalTheory.KZ.ValAt.ord_one X hτ]

def place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) : ValuationSubring X.K where
  carrier := {x | 0 ≤ ord X τ x}
  mul_mem' {x y} hx hy := by
    show 0 ≤ ord X τ (x * y)
    rw [ord_mul X hτ]
    exact add_nonneg hx hy
  one_mem' := (ord_one X hτ).ge
  add_mem' {x y} hx hy := (le_min hx hy).trans (ord_add X hτ x y)
  zero_mem' := by simpa using ord_const X hτ 0
  neg_mem' {x} hx := by
    show 0 ≤ ord X τ (-x)
    have h := ord_const X hτ (-1)
    rw [map_neg, map_one] at h
    rw [← neg_one_mul, ord_mul X hτ]
    exact add_nonneg h hx
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left
      subst hx
      show 0 ≤ ord X τ 0
      simpa using ord_const X hτ 0
    · by_contra hc
      rw [not_or] at hc
      have h1 : ord X τ x < 0 := not_le.1 hc.1
      have h2 : ord X τ x⁻¹ < 0 := not_le.1 hc.2
      have h3 := ord_add_ord_inv X hτ hx
      have h4 : ord X τ x + ord X τ x⁻¹ ≤ ord X τ x + 0 := by gcongr
      rw [h3, add_zero] at h4
      exact absurd h1 (not_lt.2 h4)

theorem mem_place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) (x : X.K) : x ∈ place X hτ ↔ 0 ≤ ord X τ x := Iff.rfl

theorem exists_place {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 →
      ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  refine ⟨place X hτ, ⟨fun c => ord_const X hτ c, ?_⟩, fun x hx φ hφ => ?_⟩
  · obtain ⟨φ, h, hφ⟩ := X.j_hol
    rw [mem_place, ord_eq X hτ h]
    exact (hφ.analyticOnNhd isOpen_Hs τ hτ).meromorphicOrderAt_nonneg
  · have h0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have h1 : 0 ≤ ord X τ x := (mem_place X hτ x).1 (((place X hτ).valuation_le_one_iff x).1 hx.le)
    have h2 : 0 ≤ ord X τ x⁻¹ := (mem_place X hτ _).1 (((place X hτ).valuation_le_one_iff _).1
      (by rw [map_inv₀, hx, inv_one]))
    have h3 := ord_add_ord_inv X hτ h0
    rw [← ord_eq X hτ hφ]
    refine le_antisymm ?_ h1
    calc ord X τ x = ord X τ x + 0 := (add_zero _).symm
      _ ≤ ord X τ x + ord X τ x⁻¹ := by gcongr
      _ = 0 := h3

end GlobalTheory.KZ.ValAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePointStatement
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlane
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ

theorem hs_isOpen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem hs_isPreconnected : IsPreconnected Hs :=
  (convex_halfSpace_im_gt (r := 0)).isPreconnected

theorem mero_eq_zero_of_eventually {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a Hs) {τ : ℂ} (hτ : τ ∈ Hs)
    (h : a =ᶠ[𝓝 τ] 0) : (a : Mero) = 0 := by
  have hE := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_isPreconnected hτ h
  exact Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => hE hz)

theorem Tower.an_meromorphicAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K)
    (φ : ℂ → ℂ) (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  have ha' : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd hs_isOpen
  have hb' : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd hs_isOpen

  rw [hφ] at hab
  have hrel : ∀ᶠ z in codiscreteWithin Hs, φ z * b z = a z := Filter.Germ.coe_eq.1 hab
  have hrel' : ∀ᶠ z in 𝓝[≠] τ, φ z * b z = a z := by
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hrel) τ hτ
    have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (hs_isOpen.mem_nhds hτ)
    filter_upwards [h1, h2] with z hz1 hz2
    rcases hz1 with hz1 | hz1
    · exact hz1
    · exact absurd hz2 hz1

  have hbne : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
    rcases (hb' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (mero_eq_zero_of_eventually hb' hτ h) hb0
    · exact h
  have heq : (fun z => a z / b z) =ᶠ[𝓝[≠] τ] φ := by
    filter_upwards [hrel', hbne] with z h1 h2
    rw [← h1, mul_div_cancel_right₀ _ h2]
  have hmer : MeromorphicAt φ τ :=
    ((ha' τ hτ).meromorphicAt.div (hb' τ hτ).meromorphicAt).congr heq
  refine ⟨hmer, fun hx htop => ?_⟩
  have hφ0 : ∀ᶠ z in 𝓝[≠] τ, φ z = 0 := meromorphicOrderAt_eq_top_iff.1 htop
  have ha0 : ∀ᶠ z in 𝓝[≠] τ, a z = 0 := by
    filter_upwards [hrel', hφ0] with z h1 h2
    rw [← h1, h2, zero_mul]
  have ha00 : a =ᶠ[𝓝 τ] 0 := by
    rcases (ha' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd ((ha0.and h).exists) (by rintro ⟨z, h1, h2⟩; exact h2 h1)
  have hA : (a : Mero) = 0 := mero_eq_zero_of_eventually ha' hτ ha00
  rw [← hφ, hA] at hab
  apply hb0
  have hu : X.an x⁻¹ * X.an x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  calc (b : Mero) = X.an x⁻¹ * X.an x * (b : Mero) := by rw [hu, one_mul]
    _ = X.an x⁻¹ * (X.an x * (b : Mero)) := by rw [mul_assoc]
    _ = 0 := by rw [hab, mul_zero]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlaneStatement
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.an_meromorphicAt_upperHalfPlane : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ), X.an x = (φ : Mero) → ∀ τ : ℂ, τ ∈ Hs → MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  first | exact @GlobalTheory.KZ.Tower.an_meromorphicAt | exact GlobalTheory.KZ.Tower.an_meromorphicAt | (intros; apply GlobalTheory.KZ.Tower.an_meromorphicAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMeromorphicRootOfMemModularFunctionTowerUn
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ.MeroRoot

theorem valAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ,
      X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point X τ hτ

theorem repAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ)
    (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := GlobalTheory.T.an_meromorphicAt_upperHalfPlane X x φ hφ τ hτ

theorem rootHs (h : ℂ → ℂ) (m : ℕ) (hm : 0 < m) (hh : DifferentiableOn ℂ h Hs)
    (hdiv : ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd h m hm hh hdiv

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_codisc {F G : ℂ → ℂ} (hFG : F =ᶠ[codiscreteWithin Hs] G) {τ : ℂ} (hτ : τ ∈ Hs) :
    F =ᶠ[𝓝[≠] τ] G := by
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hFG) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := nhdsWithin_le_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem germ_rep (x : Mero) : ∃ φ : ℂ → ℂ, x = (φ : Mero) := by
  induction x using Filter.Germ.inductionOn with
  | h φ => exact ⟨φ, rfl⟩

theorem wt_dvd {m : ℕ} (hm : 0 < m) {k : ℤ} {u v : WithTop ℤ}
    (hk : (k : WithTop ℤ) = (m : WithTop ℤ) * u + (m : WithTop ℤ) * v) : (m : ℤ) ∣ k := by
  have hm0 : (m : WithTop ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  cases u with
  | top => rw [WithTop.mul_top hm0, WithTop.top_add] at hk; exact absurd hk (WithTop.coe_ne_top)
  | coe p =>
    cases v with
    | top => rw [WithTop.mul_top hm0, WithTop.add_top] at hk; exact absurd hk (WithTop.coe_ne_top)
    | coe q =>
      have : k = (m : ℤ) * p + (m : ℤ) * q := by exact_mod_cast hk
      exact ⟨p + q, by rw [this]; ring⟩

theorem orders_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (f : X.Kˣ) (hf : f ∈ X.Un m) (a b : ℂ → ℂ) (hb : DifferentiableOn ℂ b Hs)
    (hab : X.an (f : X.K) * (b : Mero) = (a : Mero)) :
    ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt (fun z => a z * b z ^ (m - 1)) τ = (k : WithTop ℤ) → (m : ℤ) ∣ k := by
  intro τ hτ k hk
  obtain ⟨W, hW, hWv⟩ := valAt X τ hτ
  obtain ⟨g, hg⟩ := hf W hW
  obtain ⟨φf, hφf⟩ := germ_rep (X.an (f : X.K))
  obtain ⟨φg, hφg⟩ := germ_rep (X.an (g : X.K))
  obtain ⟨ψ, hψ⟩ := germ_rep (X.an ((f : X.K) / (g : X.K) ^ m))
  have hψ0 : meromorphicOrderAt ψ τ = 0 := hWv _ hg ψ hψ
  have hfm := (repAt X _ φf hφf τ hτ).1
  have hgm := (repAt X _ φg hφg τ hτ).1
  have hψm := (repAt X _ ψ hψ τ hτ).1
  have hbm : MeromorphicAt b τ :=
    ((hb.analyticOnNhd isOpen_Hs) τ hτ).meromorphicAt

  have e1 : (φf : Mero) = ((fun z => ψ z * φg z ^ m : ℂ → ℂ) : Mero) := by
    have : (f : X.K) = ((f : X.K) / (g : X.K) ^ m) * (g : X.K) ^ m := by
      rw [div_mul_cancel₀]; exact pow_ne_zero _ g.ne_zero
    rw [← hφf, this, map_mul, map_pow, hψ, hφg]; rfl
  have e1' : φf =ᶠ[𝓝[≠] τ] (fun z => ψ z * φg z ^ m) := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e1) hτ
  have e2 : ((fun z => a z * b z ^ (m - 1) : ℂ → ℂ) : Mero) = ((fun z => φf z * b z ^ m : ℂ → ℂ) : Mero) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show ((a * b ^ n : ℂ → ℂ) : Mero) = ((φf * b ^ (n + 1) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, ← hab, hφf, pow_succ]
    ring
  have e2' := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e2) hτ
  have o1 : meromorphicOrderAt φf τ = (m : WithTop ℤ) * meromorphicOrderAt φg τ := by
    rw [meromorphicOrderAt_congr e1']
    rw [show (fun z => ψ z * φg z ^ m) = ψ * φg ^ m from rfl, meromorphicOrderAt_mul hψm (hgm.pow m),
      meromorphicOrderAt_pow hgm, hψ0, zero_add]
  rw [meromorphicOrderAt_congr e2', show (fun z => φf z * b z ^ m) = φf * b ^ m from rfl,
    meromorphicOrderAt_mul hfm (hbm.pow m), meromorphicOrderAt_pow hbm, o1] at hk
  exact wt_dvd hm hk.symm

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem exists_mero_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧
      (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f hf
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero (f : X.K)
  obtain ⟨g, hg, hgm⟩ := rootHs (fun z => a z * b z ^ (m - 1)) m hm (ha.mul (hb.pow _))
    (orders_dvd X m hm f hf a b hb hab)
  refine ⟨g, b, hg, hb, hb0, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : ((fun z => a z * b z ^ n : ℂ → ℂ) : Mero) = ((fun z => g z ^ (n + 1) : ℂ → ℂ) : Mero) := by
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simpa using (hgm z hz).symm
  rw [pow_succ, mul_comm ((b : Mero) ^ n), ← mul_assoc, hab, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow,
    ← Filter.Germ.coe_mul]
  exact e

end GlobalTheory.KZ.MeroRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMeromorphicRootOfMemModularFunctionTowerUnStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_meromorphic_root_of_mem_modularFunctionTower_Un : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  first | exact @GlobalTheory.KZ.MeroRoot.exists_mero_root | exact GlobalTheory.KZ.MeroRoot.exists_mero_root | (intros; apply GlobalTheory.KZ.MeroRoot.exists_mero_root <;> assumption)
end
