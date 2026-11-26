module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRect
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectA
open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem exr_ord (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (ρ : ℂ) (hρ : ρ ∈ Zb) (hρS : ρ ∈ S) (hhρ : h ρ ≠ 0) : analyticOrderNatAt f ρ = m ρ := by
  classical
  have hne : ∀ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ' ≠ 0 := fun ρ' h' =>
    pow_ne_zero _ (sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h') e.symm)
  have hgD : DifferentiableOn ℂ (fun z => (∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) S :=
    (DifferentiableOn.fun_finsetProd fun ρ' _ => (differentiableOn_id.sub_const ρ').pow _).mul hh
  have hgA := hgD.analyticAt (hS.mem_nhds hρS)
  have hg0 : (∏ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ') * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 hne) hhρ
  have heq : ∀ z ∈ S, f z = (z - ρ) ^ m ρ * ((∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) := by
    intro z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Zb (fun ρ' => (z - ρ') ^ m ρ') hρ, mul_assoc]
  have hfA : AnalyticAt ℂ f ρ :=
    (((analyticAt_id.sub analyticAt_const).pow (m ρ)).mul hgA).congr
      (Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => (heq z hz).symm)
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hfA.analyticOrderAt_eq_natCast]
    exact ⟨_, hgA, hg0, Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => by rw [heq z hz, smul_eq_mul]⟩
  simp [analyticOrderNatAt, hord]

theorem exr_logDeriv (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (w : ℂ) (hwS : w ∈ S) (hwZ : w ∉ Zb) (hhw : h w ≠ 0) :
    deriv f w / f w = (∑ ρ ∈ Zb, (m ρ : ℂ) / (w - ρ)) + deriv h w / h w := by
  classical
  have hPd : ∀ s : Finset ℂ, w ∉ s → HasDerivAt (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ s, (w - ρ) ^ m ρ) * ∑ ρ ∈ s, (m ρ : ℂ) / (w - ρ)) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hasDerivAt_const w (1 : ℂ)
    | insert a s ha ih =>
      intro hw
      have hwa : w - a ≠ 0 := sub_ne_zero.2 fun e => hw (e ▸ Finset.mem_insert_self a s)
      have ih' := ih fun e => hw (Finset.mem_insert_of_mem e)
      have hm := (((hasDerivAt_id' w).sub_const a).pow (m a)).mul ih'
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hm.congr_deriv ?_
      simp only [Pi.pow_apply]
      rcases Nat.eq_zero_or_pos (m a) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ : ∃ k, m a = k + 1 := ⟨m a - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        push_cast
        field_simp
        ring
  have hPne : (∏ ρ ∈ Zb, (w - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ hρ => pow_ne_zero _ (sub_ne_zero.2 fun e => hwZ (e ▸ hρ))
  have hhd : HasDerivAt h (deriv h w) w := (hh.differentiableAt (hS.mem_nhds hwS)).hasDerivAt
  have hprod := (hPd Zb hwZ).mul hhd
  have hev : f =ᶠ[𝓝 w] fun z => (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem (hS.mem_nhds hwS) hfac
  have hd : deriv f w = _ := hev.deriv_eq.trans hprod.deriv
  rw [hd, hfac w hwS]
  field_simp

theorem exr_term (m e c w ρ y : ℂ) (hw : w ≠ 0) (hw1 : w - 1 ≠ 0) (hwρ : w - ρ ≠ 0)
    (hρ : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0) :
    -(m / (w - ρ)) * (e / w / (w - 1)) + m / (1 - ρ) * y / (w - 1) - (-m * (c / (ρ * (ρ - 1)))) / (w - ρ)
      + m / (ρ - 1) * ((e / w - c / ρ) / (w - ρ) - (e / w - y) / (w - 1)) = 0 := by
  have hρ1' : 1 - ρ ≠ 0 := fun e => hρ1 (by linear_combination -e)
  field_simp
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exr_abs_le {a p q : ℝ} (h1 : p ≤ a) (h2 : a ≤ q) : |a| ≤ |p| + |q| :=
  abs_le.2 ⟨by linarith [neg_abs_le p, abs_nonneg q], by linarith [le_abs_self q, abs_nonneg p]⟩

theorem ex_rect_logDeriv (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (y : ℝ) (hy : 0 < y)
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (f ρ = 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁))
    (hedge : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → f w = 0 →
      x₀ < w.re ∧ w.re < x₁ ∧ y₀ < w.im ∧ w.im < y₁) :
    Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (-(deriv f 1 / f 1) * y - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ) := by
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = |x₀ - 1| + |x₁ - 1| + |y₀| + |y₁| + 1 := ⟨_, rfl⟩
  have hR₁ : 0 < R₁ := by rw [hR₁def]; positivity
  obtain ⟨Zb, m, h, hZb, hm, hh, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f 1 (R₁ + 1) R₁ hR₁ (by linarith) hf.differentiableOn hf1
  have hrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w a1 a2 a3 a4
    rw [Metric.mem_ball, dist_eq_norm]
    have e1 := Complex.norm_le_abs_re_add_abs_im (w - 1)
    have e2 : |(w - 1).re| ≤ |x₀ - 1| + |x₁ - 1| := by
      rw [sub_re, one_re]; exact exr_abs_le (by linarith) (by linarith)
    have e3 : |(w - 1).im| ≤ |y₀| + |y₁| := by
      rw [sub_im, one_im, sub_zero]; exact exr_abs_le a3 a4
    linarith
  have hball : Metric.ball (1 : ℂ) R₁ ⊆ Metric.closedBall 1 R₁ := Metric.ball_subset_closedBall
  have hSsub : Metric.ball (1 : ℂ) (R₁ + 1) ⊆ Metric.closedBall 1 (R₁ + 1) := Metric.ball_subset_closedBall
  have hR1S : Metric.ball (1 : ℂ) R₁ ⊆ Metric.ball 1 (R₁ + 1) := Metric.ball_subset_ball (by linarith)
  have hhS : DifferentiableOn ℂ h (Metric.ball 1 (R₁ + 1)) := hh.mono hSsub
  have hfacS : ∀ z ∈ Metric.ball (1 : ℂ) (R₁ + 1), f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    fun z hz => hfac z (hSsub hz)
  have hZin : ∀ ρ ∈ Z, ρ ∈ Metric.ball (1 : ℂ) R₁ := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hrect ρ a1.le a2.le a3.le a4.le
  have hZsub : Z ⊆ Zb := by
    intro ρ hρ
    exact (hZb ρ).2 ⟨hball (hZin ρ hρ), ((hZ ρ).1 hρ).1⟩
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := fun ρ hρ =>
    exr_ord f h Zb m _ Metric.isOpen_ball hhS hfacS ρ (hZsub hρ) (hR1S (hZin ρ hρ))
      (hh0 ρ (hball (hZin ρ hρ)))
  have h1Z : (1 : ℂ) ∉ Z := fun h => hf1 ((hZ 1).1 h).1
  have hZne0 : ∀ ρ ∈ Z, ρ ≠ 0 := by
    intro ρ hρ h0; have := ((hZ ρ).1 hρ).2.1; rw [h0, zero_re] at this; linarith
  have hZne1 : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h1 => h1Z (h1 ▸ hρ)

  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = Metric.ball (1 : ℂ) R₁ \ (((Zb \ Z : Finset ℂ) : Set ℂ) ∪ {0}) :=
    ⟨_, rfl⟩
  have hU : IsOpen U := by
    rw [hUdef]
    exact Metric.isOpen_ball.sdiff ((Finset.finite_toSet _).union (Set.finite_singleton 0)).isClosed
  have hUrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ U := by
    intro w a1 a2 a3 a4
    rw [hUdef]
    refine ⟨hrect w a1 a2 a3 a4, ?_⟩
    rintro (hw | hw)
    · rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_coe] at hw
      have hfw : f w = 0 := ((hZb w).1 hw.1).2
      obtain ⟨b1, b2, b3, b4⟩ := hedge w a1 a2 a3 a4 hfw
      exact hw.2 ((hZ w).2 ⟨hfw, b1, b2, b3, b4⟩)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, zero_re] at a1; linarith
  have hUball : ∀ w ∈ U, w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w hw; rw [hUdef] at hw; exact hw.1
  have hUne0 : ∀ w ∈ U, w ≠ 0 := by
    intro w hw h0; rw [hUdef] at hw; exact hw.2 (Or.inr h0)
  have hUZb : ∀ w ∈ U, w ∉ Z → w ∉ Zb := by
    intro w hw hwZ hwZb; rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff]; exact ⟨hwZb, hwZ⟩))
  have h1U : (1 : ℂ) ∈ U := hUrect 1 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZU : ∀ ρ ∈ Z, ρ ∈ U := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hUrect ρ a1.le a2.le a3.le a4.le

  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun w => (y : ℂ) ^ w / w := ⟨_, rfl⟩
  obtain ⟨Lf, hLdef⟩ : ∃ Lf : ℂ → ℂ,
      Lf = fun w => deriv h w / h w + ∑ ρ ∈ Zb \ Z, (m ρ : ℂ) / (w - ρ) := ⟨_, rfl⟩
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hφU : DifferentiableOn ℂ φ U := by
    intro w hw
    rw [hφdef]
    exact ((differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id
      (hUne0 w hw)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ Lf U := by
    intro w hw
    have hwb := hR1S (hUball w hw)
    have hN : Metric.ball (1 : ℂ) (R₁ + 1) ∈ nhds w := Metric.isOpen_ball.mem_nhds hwb
    have hd1 : DifferentiableAt ℂ (deriv h) w :=
      ((hhS.deriv Metric.isOpen_ball) w hwb).differentiableAt hN
    have hd2 : DifferentiableAt ℂ h w := (hhS w hwb).differentiableAt hN
    have hhw : h w ≠ 0 := hh0 w (hball (hUball w hw))
    rw [hLdef]
    refine (DifferentiableAt.add (hd1.div hd2 hhw) ?_).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun ρ hρ => ?_
    refine (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) ?_
    rw [Finset.mem_sdiff] at hρ
    intro h0; rw [sub_eq_zero] at h0
    rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff, h0]; exact ⟨hρ.1, hρ.2⟩))
  have hLD : ∀ w ∈ U, w ∉ Z → deriv f w / f w = (∑ ρ ∈ Z, (m ρ : ℂ) / (w - ρ)) + Lf w := by
    intro w hw hwZ
    rw [exr_logDeriv f h Zb m _ Metric.isOpen_ball hhS hfacS w (hR1S (hUball w hw)) (hUZb w hw hwZ)
      (hh0 w (hball (hUball w hw))), hLdef, ← Finset.sum_sdiff hZsub]
    ring
  have hk : ∀ w, exKer y w = φ w / (w - 1) := fun w => by rw [hφdef, exKer, div_div]
  have hb1 : ∃ b : ℂ → ℂ, b 1 = -(deriv f 1 / f 1) * y ∧ ∀ ρ ∈ Z, b ρ = -(m ρ : ℂ) * exKer y ρ :=
    ⟨fun p => if p = 1 then -(deriv f 1 / f 1) * y else -(m p : ℂ) * exKer y p, by simp,
      fun ρ hρ => by simp [hZne1 ρ hρ]⟩
  obtain ⟨b, hb1, hbρ⟩ := hb1
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : ℂ → ℂ, G₀ = fun w => -dslope (fun z => Lf z * φ z) 1 w -
      ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := ⟨_, rfl⟩
  have hG₀U : DifferentiableOn ℂ G₀ U := by
    rw [hG₀def]
    refine DifferentiableOn.sub ((differentiableOn_dslope (hU.mem_nhds h1U)).2 (hLU.mul hφU)).neg ?_
    refine DifferentiableOn.fun_sum fun ρ hρ => ?_
    exact (differentiableOn_const _).mul (((differentiableOn_dslope (hU.mem_nhds (hZU ρ hρ))).2 hφU).sub
      ((differentiableOn_dslope (hU.mem_nhds h1U)).2 hφU))
  have hφw : ∀ z, φ z = (y : ℂ) ^ z / z := fun z => by rw [hφdef]
  have hφ1 : φ 1 = y := by rw [hφw]; simp
  have hkey : ∀ w ∈ U, w ∉ insert 1 Z →
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) = G₀ w := by
    intro w hw hwP
    rw [Finset.mem_insert, not_or] at hwP
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hwP.1
    have hw0 := hUne0 w hw
    have hwρ : ∀ ρ ∈ Z, w - ρ ≠ 0 := fun ρ hρ h0 => hwP.2 (sub_eq_zero.1 h0 ▸ hρ)
    have hC : ∑ ρ ∈ Z, b ρ / (w - ρ) = ∑ ρ ∈ Z, -(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1))) / (w - ρ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, exKer]
    have hD : ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) =
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1)) :=
      Finset.sum_congr rfl fun ρ hρ => by
        rw [dslope_of_ne _ (sub_ne_zero.1 (hwρ ρ hρ)), dslope_of_ne _ hwP.1, slope_def_field,
          slope_def_field, hφ1, hφw, hφw]
    have hrel : ∑ ρ ∈ Z, (-((m ρ : ℂ) / (w - ρ)) * ((y : ℂ) ^ w / w / (w - 1)) +
        (m ρ : ℂ) / (1 - ρ) * y / (w - 1) - (-(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1)))) / (w - ρ) +
        (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1))) = 0 :=
      Finset.sum_eq_zero fun ρ hρ => exr_term _ _ _ _ _ _ hw0 hw1 (hwρ ρ hρ) (hZne0 ρ hρ)
        (sub_ne_zero.2 (hZne1 ρ hρ))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hrel
    have hG₀w : G₀ w = -dslope (fun z => Lf z * φ z) 1 w -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := by rw [hG₀def]
    rw [hG₀w, hD, Finset.sum_insert h1Z, hC, hb1, dslope_of_ne _ hwP.1, slope_def_field, hLD w hw hwP.2,
      hLD 1 h1U h1Z, hk w, hφ1, hφw w]
    linear_combination hrel
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun w => if w ∈ insert 1 Z then G₀ w else
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) := ⟨_, rfl⟩
  have hGU : DifferentiableOn ℂ G U := by
    refine hG₀U.congr fun w hw => ?_
    rw [hGdef]
    by_cases hwP : w ∈ insert 1 Z
    · simp only [if_pos hwP]
    · simp only [if_neg hwP]; exact hkey w hw hwP
  have hPin : ∀ p ∈ insert 1 Z, x₀ < p.re ∧ p.re < x₁ ∧ y₀ < p.im ∧ p.im < y₁ := by
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with hp | hp
    · subst hp; simp; exact ⟨hx₀1, hx₁, hy₀, hy₁⟩
    · exact ((hZ p).1 hp).2
  have hsub : (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    exact hUrect w hw.1.1 hw.1.2 hw.2.1 hw.2.2
  have hres := Formalism.FX.rectangle_residue (fun w => -(deriv f w / f w) * exKer y w) G (insert 1 Z) b
    x₀ x₁ y₀ y₁ (by linarith) (by linarith) hPin ⟨U, hU, hsub, hGU⟩ (fun w hw => by
      rw [hGdef]; simp only [if_neg hw]; ring)
  have hsum : ∑ ρ ∈ Z, b ρ = -∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, hord ρ hρ, neg_mul]
  rw [show Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
    Formalism.FX.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ from rfl, hres,
    Finset.sum_insert h1Z, hb1, hsum]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_phi_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := by
  have h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have h2 := h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 =
      (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [Complex.cpow_one, ← Complex.ofReal_log hy.le]
    ring
  exact h2.congr_deriv e

theorem ex_phi_differentiableOn (y : ℝ) (hy : 0 < y) :
    DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  exact ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div differentiableAt_id hw0).differentiableWithinAt

theorem ex_rect_double (y : ℝ) (hy : 0 < y) (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    Formalism.ZF.rectInt (fun w => exKer y w / (w - 1)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * ((y : ℂ) * (Real.log y : ℂ) - y) := by
  have hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := ex_phi_hasDerivAt y hy
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hU.mem_nhds (by simp)
  have hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := ex_phi_differentiableOn y hy
  have hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)
  have hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [dslope_same, hb.deriv]
  refine Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1))
    (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁
    (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)
    ⟨{w : ℂ | 0 < w.re}, hU, ?_, hG⟩ ?_
  · intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    show 0 < z.re
    linarith [hz.1.1]
  · intro w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]
    simp only [exKer, Complex.cpow_one, div_one]
    by_cases h0 : w = 0
    · subst h0
      simp
      ring
    · field_simp
      ring

def exBdry (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ ≤ w.re ∧ w.re ≤ x₁ ∧ y₀ ≤ w.im ∧ w.im ≤ y₁ ∧
    (w.re = x₀ ∨ w.re = x₁ ∨ w.im = y₀ ∨ w.im = y₁)}

theorem ex_mem_horiz {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = y₀ ∨ c = y₁) {x : ℝ}
    (h : x ∈ Set.uIcc x₀ x₁) : ((x : ℂ) + c * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hx] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : y₀ ≤ c ∧ c ≤ y₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩
  right; right
  simpa using hc

theorem ex_mem_vert {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = x₀ ∨ c = x₁) {t : ℝ}
    (h : t ∈ Set.uIcc y₀ y₁) : ((c : ℂ) + t * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hy] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : x₀ ≤ c ∧ c ≤ x₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩
  rcases hc with hc | hc
  · left
    simpa using hc
  · right; left
    simpa using hc

theorem ex_rectInt_congr {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ w ∈ exBdry x₀ x₁ y₀ y₁, f w = g w) :
    Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ = Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  have hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')
  have hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) →
      (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)
  unfold Formalism.ZF.rectInt
  rw [hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]

theorem ex_ii_horiz {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = y₀ ∨ c = y₁) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn
    fun x hx' => ex_mem_horiz hx hy hc hx'

theorem ex_ii_vert {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = x₀ ∨ c = x₁) :
    IntervalIntegrable (fun t : ℝ => f (c + t * I)) MeasureTheory.volume y₀ y₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousOn
    fun t ht => ex_mem_vert hx hy hc ht

theorem ex_rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  unfold Formalism.ZF.rectInt
  rw [intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)),
    intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_vert hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inl rfl)) (ex_ii_vert hx hy hg (Or.inl rfl))]
  ring

theorem exKer_continuousAt (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ContinuousAt (exKer y) w := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold exKer
  apply ContinuousAt.div₀
  · exact continuousAt_const_cpow hy0
  · fun_prop
  · exact mul_ne_zero h0 (sub_ne_zero.mpr h1)

theorem ex_bdry_ne {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  constructor
  · rintro rfl
    simp at h1
    linarith
  · rintro rfl
    simp at h5
    rcases h5 with h | h | h | h <;> linarith

private theorem neg_div_mul_eq_neg_add_div_mul_add_div (a b K u : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) :
    -(b / a) * K = -((1 * a + u * b) / (u * a)) * K + K / u := by
  field_simp
  ring

set_option maxHeartbeats 800000 in
theorem ex_rect_Fchi {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by
  have hfd : Differentiable ℂ (exLF χ) := exLF_differentiable χ
  have hx : σ₁ ≤ σ₀ := by linarith
  have hyy : -T' ≤ T' := by linarith
  have hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T' := by
    intro ρ
    rw [hZ ρ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have := exLF_re_lt_one χ h0
      exact ⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩
    · rintro ⟨h0, h1, -, h3, h4⟩
      exact ⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩
  have hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 →
      σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T' := by
    intro w h1 h2 h3 h4 h0
    obtain ⟨h5, h6⟩ := hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0
    have := exLF_re_lt_one χ h0
    exact ⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩
  have hmain := ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀
    (by linarith) hT' Z hZ' hedge'
  by_cases hχ : χ = 1
  · subst hχ
    have hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0 := by
      intro w hw
      obtain ⟨h0, h1⟩ := ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw
      refine ⟨h0, h1, fun hfw => ?_⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hedge' w a1 a2 a3 a4 hfw
      rcases a5 with h | h | h | h <;> linarith
    have hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w /
        exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w :=
        (hfd.analyticAt w).deriv.continuousAt
      exact (((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt
    have hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, -⟩ := hbd w hw
      have hs : ContinuousAt (fun s : ℂ => s - 1) w := continuousAt_id.sub continuousAt_const
      exact ((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt
    have hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w =
        -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w +
          exKer y w / (w - 1) := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hfw : exLF (1 : DirichletCharacter ℂ M) w =
          (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := exLF_one_char_apply h1
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0 := by
        intro h
        apply h2
        rw [hfw, h, mul_zero]
      have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w :=
        DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)
      have hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w]
          fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s :=
        (eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs
      have hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w =
          1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w +
            (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w := by
        rw [hev.deriv_eq]
        exact (((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv
      have e1 : Fchi (1 : DirichletCharacter ℂ M) y w =
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w := by
        simp only [Fchi, negLD, exKer, mul_div_assoc]
      rw [e1, hder, hfw]
      exact neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1
    rw [ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain,
      ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]
    simp only [explicitFormulaConstant, exOrd]
    ring
  · have hfL : exLF χ = DirichletCharacter.LFunction χ := exLF_of_ne hχ
    have hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w := by
      funext w
      simp only [Fchi, negLD, exKer, hfL, mul_div_assoc]
    rw [hF, hmain, if_neg hχ]
    simp only [explicitFormulaConstant, exOrd]
    ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
