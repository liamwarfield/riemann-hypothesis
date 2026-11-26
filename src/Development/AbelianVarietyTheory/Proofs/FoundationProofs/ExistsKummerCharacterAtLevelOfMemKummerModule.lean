module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRoot
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_natCast (m k : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ZMod m).val : ℕ) : ℂ) / (m : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_natCast]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk : 2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((k % m : ℕ) : ℂ) / (m : ℂ) + ((k / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    push_cast
    field_simp
  rw [hk, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_of_isRoot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f →
    IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ n x f a b hx hr
  obtain ⟨G1, -, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨M1, -, -, M4, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨ha, hb, hb0, hab0⟩ := hr
  have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  obtain ⟨M, hM, hlev⟩ := X.level (f : X.K)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (f : X.K)) (fun φ => ⟨φ, rfl⟩)
  have hab : (φ : Mero) * (b : Mero) ^ (l ^ n) = (a : Mero) ^ (l ^ n) := by rw [← hφ]; exact hab0
  have key : ∀ δ ∈ CongruenceSubgroup.Gamma M, ∃ k : ℕ, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) * (a z * b (mob (ofSL δ) z)) := by
    intro δ hδ
    have hφg : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = (φ : Mero) := by
      rw [← X.an_sl (ofSL δ) (f : X.K) φ hφ, hlev δ hδ, hφ]
    have dag : DifferentiableOn ℂ (fun z => a (mob (ofSL δ) z)) Hs :=
      ha.comp (M4 _) (fun z hz => M1 _ z hz)
    have dbg : DifferentiableOn ℂ (fun z => b (mob (ofSL δ) z)) Hs :=
      hb.comp (M4 _) (fun z hz => M1 _ z hz)
    have h1 : ((φ * b ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab
    have h2 : (((fun z => φ (mob (ofSL δ) z)) * (fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((fun z => a (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := G3 (ofSL δ) _ _ h1
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, hφg] at h2
    have h3 : ((((fun z => a (mob (ofSL δ) z)) * b) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((a * fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Filter.Germ.coe_mul, Filter.Germ.coe_mul]
      linear_combination (-(b : Mero) ^ (l ^ n)) * h2 +
        ((fun z => b (mob (ofSL δ) z) : ℂ → ℂ) : Mero) ^ (l ^ n) * hab
    have h4 := (G1 _ _ ((dag.mul hb).pow _) ((ha.mul dbg).pow _)).1 h3
    obtain ⟨k, hk⟩ := G5 (l ^ n) ((fun z => a (mob (ofSL δ) z)) * b) (a * fun z => b (mob (ofSL δ) z)) hm
      (dag.mul hb) (ha.mul dbg) h4
    exact ⟨k, hk⟩
  classical
  let χ : SL(2, ℤ) → ZMod (l ^ n) := fun δ =>
    if h : δ ∈ CongruenceSubgroup.Gamma M then ((key δ h).choose : ZMod (l ^ n)) else 0
  refine ⟨χ, f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab0⟩, fun δ hδ z hz => ?_⟩
  have hc : ((l : ℂ) ^ n) = ((l ^ n : ℕ) : ℂ) := by push_cast; rfl
  simp only [χ, dif_pos hδ]
  rw [hc, exp_val_natCast (l ^ n) _ hm]
  exact (key δ hδ).choose_spec z hz

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRootStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.kum_of_isRoot | exact GlobalTheory.KZ.H3.kum_of_isRoot | (intros; apply GlobalTheory.KZ.H3.kum_of_isRoot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlane
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.UHPRoot

noncomputable def cen (k : ℕ) : ℂ := ((k : ℂ) + 2) * Complex.I

noncomputable def rad (k : ℕ) : ℝ := ((k : ℝ) + 2) - 1 / ((k : ℝ) + 2)

theorem rad_pos (k : ℕ) : 0 < rad k := by
  unfold rad
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h : 1 / ((k : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith

theorem cen_im (k : ℕ) : (cen k).im = (k : ℝ) + 2 := by simp [cen]
theorem cen_re (k : ℕ) : (cen k).re = 0 := by simp [cen]

theorem closedBall_sub (k : ℕ) : Metric.closedBall (cen k) (rad k) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_im_le_norm (z - cen k)
  have h2 : (z - cen k).im = z.im - ((k : ℝ) + 2) := by rw [Complex.sub_im, cen_im]
  rw [h2] at h1
  have h3 : 0 < 1 / ((k : ℝ) + 2) := by positivity
  show 0 < z.im
  unfold rad at hz
  have := neg_abs_le (z.im - ((k : ℝ) + 2))
  linarith

theorem ball_mono : Monotone (fun k : ℕ => Metric.ball (cen k) (rad k)) := by
  refine monotone_nat_of_le_succ fun k => Metric.ball_subset_ball' ?_
  have hd : cen k - cen (k + 1) = -Complex.I := by
    simp only [cen]; push_cast; ring
  rw [dist_eq_norm, hd, norm_neg, Complex.norm_I]
  unfold rad
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 1 / ((k : ℝ) + 1 + 2) ≤ 1 / ((k : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cover (z : ℂ) (hz : z ∈ Hs) : ∃ k : ℕ, z ∈ Metric.ball (cen k) (rad k) := by
  have hy : 0 < z.im := hz
  obtain ⟨k, hk⟩ := exists_nat_gt ((z.re ^ 2 + z.im ^ 2 + 2) / (2 * z.im))
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := (k : ℝ) + 2 with ha
  have hapos : 0 < a := by positivity
  have hka : (k : ℝ) < a := by linarith
  have h1 : z.re ^ 2 + z.im ^ 2 + 2 < 2 * z.im * a := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * z.im)).1 (hk.trans hka)
    linarith
  have hsq : ‖z - cen k‖ ^ 2 = z.re ^ 2 + (z.im - a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, cen_re, cen_im]
    ring
  have hrad : rad k = a - 1 / a := rfl
  have hinv : a * (1 / a) = 1 := by field_simp
  have hlt : ‖z - cen k‖ ^ 2 < rad k ^ 2 := by
    rw [hsq, hrad]
    nlinarith [sq_nonneg (1 / a)]
  exact lt_of_pow_lt_pow_left₀ 2 (rad_pos k).le hlt

theorem eqOn_of_pow_eq {D : Set ℂ} (hD : IsOpen D) (hc : IsPreconnected D) {m : ℕ} (hm : 0 < m)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    {z0 : ℂ} (hz0 : z0 ∈ D) (hfg0 : f z0 = g z0) (hne : f z0 ≠ 0)
    (hpow : ∀ z ∈ D, f z ^ m = g z ^ m) : Set.EqOn f g D := by
  have hfc : ContinuousAt f z0 := (hf.differentiableAt (hD.mem_nhds hz0)).continuousAt
  have hgc : ContinuousAt g z0 := (hg.differentiableAt (hD.mem_nhds hz0)).continuousAt
  set S : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, f z ^ i * g z ^ (m - 1 - i) with hS
  have hSc : ContinuousAt S z0 := by
    simp only [hS]; fun_prop
  have hS0 : S z0 ≠ 0 := by
    have : S z0 = (m : ℂ) * f z0 ^ (m - 1) := by
      simp only [hS, ← hfg0]
      rw [Finset.sum_congr rfl (g := fun _ => f z0 ^ (m - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [this]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hne)
  have hev : f =ᶠ[nhds z0] g := by
    filter_upwards [hSc.eventually_ne hS0, hD.mem_nhds hz0] with z hz hzD
    have key : S z * (f z - g z) = f z ^ m - g z ^ m := by
      simp only [hS]; exact geom_sum₂_mul (f z) (g z) m
    rw [hpow z hzD, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hz)
  exact (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hD) hc hz0 hev

end GlobalTheory.UHPRoot


open GlobalTheory.UHPRoot in
theorem GlobalTheory.KZ.H3.uhp_root : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  classical
  intro h m hm hd hord
  have hHo : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ h Hs := hd.analyticOnNhd hHo
  have hr : ∀ k : ℕ, ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball (cen k) (rad k)) ∧
      ∀ z ∈ Metric.ball (cen k) (rad k), r z ^ m = h z := fun k =>
    GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd h m (cen k) (rad k) hm (rad_pos k) (han.mono (closedBall_sub k))
      (fun τ hτ => hord τ (closedBall_sub k hτ))
  choose r hrd hrp using hr

  have hc0 : cen 0 ∈ Hs := closedBall_sub 0 (Metric.mem_closedBall_self (rad_pos 0).le)
  obtain ⟨k0, hk0⟩ := hord (cen 0) hc0
  have hnt : ¬ ∀ᶠ z in nhds (cen 0), h z = 0 := by
    rw [← analyticOrderAt_eq_top, hk0]; exact ENat.coe_ne_top _
  obtain ⟨z0, hz0h, hz0D⟩ := ((Filter.not_eventually.1 hnt).and_eventually
    (Metric.ball_mem_nhds (cen 0) (rad_pos 0))).exists
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq (h z0) hm
  have hw0ne : w0 ≠ 0 := by
    rintro rfl; rw [zero_pow hm.ne'] at hw0; exact hz0h hw0.symm
  have hz0k : ∀ k, z0 ∈ Metric.ball (cen k) (rad k) := fun k => ball_mono (Nat.zero_le k) hz0D
  have hrk0 : ∀ k, r k z0 ≠ 0 := by
    intro k h0; have := hrp k z0 (hz0k k); rw [h0, zero_pow hm.ne'] at this; exact hz0h this.symm

  set r' : ℕ → ℂ → ℂ := fun k z => (w0 / r k z0) * r k z with hr'
  have hr'd : ∀ k, DifferentiableOn ℂ (r' k) (Metric.ball (cen k) (rad k)) := fun k =>
    (differentiableOn_const _).mul (hrd k)
  have hr'p : ∀ k, ∀ z ∈ Metric.ball (cen k) (rad k), r' k z ^ m = h z := by
    intro k z hz
    simp only [hr', mul_pow, div_pow, hw0, hrp k z hz, hrp k z0 (hz0k k)]
    rw [div_self hz0h, one_mul]
  have hr'0 : ∀ k, r' k z0 = w0 := by
    intro k; simp only [hr']; rw [div_mul_cancel₀ _ (hrk0 k)]
  have agree_le : ∀ j k, j ≤ k → Set.EqOn (r' j) (r' k) (Metric.ball (cen j) (rad j)) := by
    intro j k hjk
    refine eqOn_of_pow_eq Metric.isOpen_ball (convex_ball _ _).isPreconnected hm (hr'd j)
      ((hr'd k).mono (ball_mono hjk)) (hz0k j) (by rw [hr'0, hr'0]) (by rw [hr'0]; exact hw0ne) ?_
    intro z hz; rw [hr'p j z hz, hr'p k z (ball_mono hjk hz)]
  have agree : ∀ j k w, w ∈ Metric.ball (cen j) (rad j) → w ∈ Metric.ball (cen k) (rad k) →
      r' j w = r' k w := by
    intro j k w hj hk
    rcases le_total j k with hjk | hkj
    · exact agree_le j k hjk hj
    · exact (agree_le k j hkj hk).symm
  choose N hN using cover
  let R : ℂ → ℂ := fun z => if hz : z ∈ Hs then r' (N z hz) z else 0
  refine ⟨R, ?_, ?_⟩
  · intro z hz
    have hzk := hN z hz
    have hev : R =ᶠ[nhds z] r' (N z hz) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzk] with w hw
      have hwH : w ∈ Hs := closedBall_sub _ (Metric.ball_subset_closedBall hw)
      simp only [R, dif_pos hwH]
      exact agree _ _ w (hN w hwH) hw
    exact (((hr'd _).differentiableAt (Metric.isOpen_ball.mem_nhds hzk)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    simp only [R, dif_pos hz]
    exact hr'p _ z (hN z hz)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.H3.uhp_root | exact GlobalTheory.KZ.H3.uhp_root | (intros; apply GlobalTheory.KZ.H3.uhp_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.H3.UnRoot

lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected

lemma eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) {τ : ℂ} (hτ : τ ∈ Hs) :
    ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  have h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z := Filter.Germ.coe_eq.mp h
  rw [Filter.eventually_iff, mem_codiscreteWithin] at h'
  have hd := Filter.disjoint_principal_right.mp (h' τ hτ)
  have hH : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [hH, hd] with z hz1 hz2
  by_contra hne
  exact hz2 ⟨hz1, hne⟩

lemma eq_nhds_of_punctured {F G : ℂ → ℂ} {τ : ℂ} (hF : ContinuousAt F τ) (hG : ContinuousAt G τ)
    (h : ∀ᶠ z in 𝓝[≠] τ, F z = G z) : F =ᶠ[𝓝 τ] G := by
  have hτ : F τ = G τ :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))
  have h2 := eventually_nhdsWithin_iff.mp h
  filter_upwards [h2] with z hz
  by_cases hz' : z = τ
  · subst hz'; exact hτ
  · exact hz hz'

lemma order_ne_top {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) ≠ 0) {τ : ℂ} (hτ : τ ∈ Hs) :
    analyticOrderAt a τ ≠ ⊤ := by
  intro htop
  apply h0
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ
    (analyticOrderAt_eq_top.mp htop)
  have : ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z :=
    Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'
  rw [← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr this

lemma germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma num_ne_zero (X : Tower Ω ε) (f : X.Kˣ) {a b : ℂ → ℂ} (hb : (b : Mero) ≠ 0)
    (hf : X.an (f : X.K) * (b : Mero) = (a : Mero)) : (a : Mero) ≠ 0 := by
  intro h
  apply hb
  have e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc (b : Mero) = X.an ((f⁻¹ : X.Kˣ) : X.K) * (X.an (f : X.K) * b) := by rw [← mul_assoc, e, one_mul]
    _ = 0 := by rw [hf, h, mul_zero]

end GlobalTheory.KZ.H3.UnRoot

namespace GlobalTheory.KZ.H3.UnRoot

theorem exists_isRoot_of_mem_Un : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), JHol X →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  intro Ω _ _ ε X hj m hm f hf
  obtain ⟨a0, b0, ha0, hb0, hb0ne, hf0⟩ := X.an_mero (f : X.K)
  have ha0ne : (a0 : Mero) ≠ 0 := num_ne_zero X f hb0ne hf0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ :=
    fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ
  have hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞) := by
    intro τ hτ
    obtain ⟨W, hW, hWmem⟩ := GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point Ω ε X hj τ hτ
    obtain ⟨g, hg⟩ := hf W hW
    set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu
    have hgm : (g : X.K) ^ (m' + 1) ≠ 0 := pow_ne_zero _ g.ne_zero
    have hune : u ≠ 0 := div_ne_zero f.ne_zero hgm
    have huW : u ∈ W := (W.valuation_le_one_iff u).mp hg.le
    have huW' : u⁻¹ ∈ W := (W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])
    obtain ⟨φ, hφ, hφa⟩ := (hWmem u).mp huW
    obtain ⟨ψ, hψ, hψa⟩ := (hWmem u⁻¹).mp huW'

    have hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]
    have hφτ : φ τ ≠ 0 := by
      have e : φ τ * ψ τ = 1 := (eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const
        (eventually_of_germ_eq hφψ hτ)).self_of_nhds
      intro h0
      rw [h0, zero_mul] at e
      exact zero_ne_one e

    obtain ⟨a1, b1, ha1, hb1, hb1ne, hg1⟩ := X.an_mero (g : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := num_ne_zero X g hb1ne hg1
    have hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1) := by
      rw [← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]
    have hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero) := by
      simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
      rw [← hf0, ← hg1, hfu, hφ]
      ring
    have hev := eq_nhds_of_punctured
      ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _))
      ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt)
      (eventually_of_germ_eq hgerm hτ)
    have hcong := analyticOrderAt_congr hev
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ),
      analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ),
      analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ),
      hφa.analyticOrderAt_eq_zero.mpr hφτ] at hcong
    obtain ⟨oA0, orbitMap_conj_smul_zero⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)
    obtain ⟨oB0, eB0⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)
    obtain ⟨oA1, orbitMap_conj_smul_one⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)
    obtain ⟨oB1, eB1⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)
    rw [← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1] at hcong
    have heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0 := by
      simp only [nsmul_eq_mul, zero_add] at hcong
      exact_mod_cast hcong
    have hdvd : (m' + 1) ∣ oA0 + m' * oB0 :=
      Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        push_cast at this ⊢
        linear_combination this⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ),
      ← orbitMap_conj_smul_zero, ← eB0, ← hk]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨r, hr, hrm⟩ := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord
  refine ⟨r, b0, hr, hb0, hb0ne, ?_⟩
  have e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero) :=
    germ_eq_of_eqOn fun z hz => by simpa using hrm z hz
  simp only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢
  rw [e1, ← hf0]
  ring

end GlobalTheory.KZ.H3.UnRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUnStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModule
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.exists_kum_of_mem_A : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ hJ n x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, he⟩ := hy n
    have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    obtain ⟨a, b, hab⟩ := GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol Ω ε X hJ (l ^ n) hm f hf
    exact GlobalTheory.T.exists_kummerCharacter_of_upperHalfPlane_root Ω ε X l n y f a b he hab
  | zero => exact ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1⟩
  | add y z _ _ hy hz =>
    obtain ⟨χ, hχ⟩ := hy
    obtain ⟨χ', hχ'⟩ := hz
    exact ⟨χ + χ', (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 y z χ χ' hχ hχ'⟩
  | smul c y _ hy =>
    obtain ⟨χ, hχ⟩ := hy
    exact ⟨_, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c y χ hχ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModuleStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.exists_kum_of_mem_A | exact GlobalTheory.KZ.H3.exists_kum_of_mem_A | (intros; apply GlobalTheory.KZ.H3.exists_kum_of_mem_A <;> assumption)
end
