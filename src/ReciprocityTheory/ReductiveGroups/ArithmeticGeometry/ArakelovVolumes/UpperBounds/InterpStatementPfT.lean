module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfS
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfR
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfQ
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nsq_eq_normSq (s : Fin (nd X) → Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) = HE.nsq (fun k z => s k (cpt X x0 z)) z := by
  unfold HE.nsq
  exact Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_norm_sq _).symm

theorem lhs_finite (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb)
    (ε : ℝ) (hε : 0 < ε)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) (N : Set (Frame X.Ψ r))
    (hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ N → z ∉ closedBall (0 : V (nd X)) (2 * ε)) :
    ∫⁻ z, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ∂muF X x0 < ⊤ := by
  rw [muF_lintegral]
  have hO := ExF.isOpen_OmF X x0
  have hpt : ∀ᵐ z ∂(volume.restrict (OmF X x0)),
      ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ≤
        ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by
    rw [ae_restrict_iff' hO.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz0 hz
    by_cases hzN : cpt X x0 z ∈ N
    swap
    · rw [Set.indicator_of_notMem hzN, mul_zero]; exact zero_le
    rw [Set.indicator_of_mem hzN]
    have hx : cpt X x0 z ∈ X.dom := hz
    have hN : 0 < HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z := by
      rcases (HE.nsq_nonneg _ z).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hz, h.symm⟩ hz0
    have hcut : HE.cut ε hε z = 0 := HE.cut_zero ε hε (by
      have := hN2 z hz hzN
      rw [mem_closedBall, dist_zero_right, not_le] at this; exact this.le)
    set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 with hSdef
    have hS : S = HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z * Real.exp (-phla X Xa.L (cpt X x0 z)) :=
      pnorm_sum_eq X Xa.L Fl.s hx
    have hSpos : 0 < S := by rw [hS]; positivity
    have hrho := rhoF_eq X x0 Xa.Fp Xa.L ψ bb Fl.s hz hN
    rw [← hSdef] at hrho
    rw [gφ_dom X P Xa.Fp Xa.L Fl.s hx, ← hSdef, ← ENNReal.ofReal_inv_of_pos hSpos,
      ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
      ← ENNReal.ofReal_mul (densF_pos X x0 hz).le,
      ← ENNReal.ofReal_mul (mul_nonneg (densF_pos X x0 hz).le (by positivity)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [hPF z hz, hcut, zero_sub, norm_neg]
    have hd := densF_pos X x0 hz
    have hrho2 : rhoF X x0 Xa.Fp ψ bb z = Real.exp (-phla X Xa.Fp (cpt X x0 z)) *
        Real.exp (-ψ (cpt X x0 z)) * Real.exp (bb * rhF X x0 z) * densF X x0 z := by
      rw [rhoF, Real.exp_add, Real.exp_add, Real.exp_log hd, neg_add, Real.exp_add]
    have hSn : S⁻¹ ^ (nd X) = (S ^ (nd X : ℝ))⁻¹ := by
      rw [Real.rpow_natCast, inv_pow]
    have hSn0 : 0 < S ^ (nd X : ℝ) := Real.rpow_pos_of_pos hSpos _
    set A := Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
      HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ)) with hAdef
    have hA0 : 0 ≤ A := by positivity

    have key : densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X) =
        A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) := by
      have e1 : A = rhoF X x0 Xa.Fp ψ bb z / S ^ (nd X : ℝ) := by
        rw [hrho]; field_simp
      rw [e1, hrho2, hSn]
      have h1 : Real.exp (-ψ (cpt X x0 z)) * Real.exp (ψ (cpt X x0 z)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : Real.exp (bb * rhF X x0 z) * Real.exp (-(bb * rhF X x0 z)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      field_simp
      nlinarith [h1, h2]
    have hle : A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) ≤ Real.exp C0 * A := by
      have e2 : Real.exp (ψ (cpt X x0 z)) ≤ Real.exp C0 := Real.exp_le_exp.2 (hψb _ hx)
      have e3 : Real.exp (-(bb * rhF X x0 z)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
      have e4 := (Real.exp_pos (-(bb * rhF X x0 z))).le
      calc A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z))
          ≤ A * Real.exp C0 * 1 := by gcongr
        _ = Real.exp C0 * A := by ring
    have hF2 : 0 ≤ ‖F z‖ ^ 2 := sq_nonneg _
    calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x0 z))) * S⁻¹ ^ (nd X)
        = ‖F z‖ ^ 2 * (densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X)) := by ring
      _ ≤ ‖F z‖ ^ 2 * (Real.exp C0 * A) := by rw [key]; exact mul_le_mul_of_nonneg_left hle hF2
      _ = Real.exp C0 * (‖F z‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
            HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by rw [hAdef]; ring
  calc ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z)
      ≤ ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp C0) * ∫⁻ z in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem rhs_bound (x1 : Frame X.Ψ r) (Xa : ArchInM X) (Fl : FlatM X Xa) (P : Frame X.Ψ r → ℂ)
    (N : Set (Frame X.Ψ r)) (ρ1 : ℝ) (hρ1 : 0 < ρ1) (hcb : closedBall (0 : V (nd X)) ρ1 ⊆ OmF X x1)
    (hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ1, cpt X x1 w ∈ N) :
    ∃ c1 : ℝ, 0 < c1 ∧ ENNReal.ofReal c1 * ∫⁻ w in ball (0 : V (nd X)) ρ1,
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ∫⁻ w, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) ∂muF X x1 := by
  set h1 : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X Xa.Fp (cpt X x1 w) +
    (nd X : ℝ) * phla X Xa.L (cpt X x1 w)) with hh1
  have hc : ContinuousOn h1 (closedBall (0 : V (nd X)) ρ1) := fun w hw =>
    (Real.continuous_exp.continuousAt.comp ((((logDens_cdAt X x1 (hcb hw)).sub
      (phla_cpt_cdAt X x1 (hcb hw) Xa.Fp)).add (contDiffAt_const.mul
        (phla_cpt_cdAt X x1 (hcb hw) Xa.L))).continuousAt)).continuousWithinAt
  obtain ⟨w0, hw0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ1).exists_isMinOn
    ⟨0, mem_closedBall_self hρ1.le⟩ hc
  refine ⟨h1 w0, Real.exp_pos _, ?_⟩
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := by
    intro w hw
    have hwO := hcb (ball_subset_closedBall hw)
    have hx : cpt X x1 w ∈ X.dom := hwO
    rw [Set.indicator_of_mem (hN1 w hw), gφ_dom X P Xa.Fp Xa.L Fl.s hx, nsq_eq_normSq]
    set n2 := HE.nsq (fun k z => Fl.s k (cpt X x1 z)) w with hn2
    rcases (HE.nsq_nonneg (fun k z => Fl.s k (cpt X x1 z)) w).lt_or_eq with hN | hN
    · have hN' : 0 < n2 := hN
      set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x1 w) ^ 2 with hSdef
      have hS : S = n2 * Real.exp (-phla X Xa.L (cpt X x1 w)) := pnorm_sum_eq X Xa.L Fl.s hx
      have hSpos : 0 < S := by rw [hS]; positivity
      have hd := densF_pos X x1 hwO
      rw [← ENNReal.ofReal_inv_of_pos hSpos, ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
        ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le (by positivity)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hid : densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) * S⁻¹ ^ (nd X) =
          h1 w * n2 ^ (-(nd X : ℝ)) := by
        have e1 : h1 w = densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
            Real.exp (phla X Xa.L (cpt X x1 w)) ^ (nd X) := by
          simp only [hh1]
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hd, Real.exp_neg, Real.exp_nat_mul]
          ring
        rw [e1, hS, Real.rpow_neg hN'.le, Real.rpow_natCast, mul_inv, mul_pow,
          show (Real.exp (-phla X Xa.L (cpt X x1 w)))⁻¹ = Real.exp (phla X Xa.L (cpt X x1 w)) by
            rw [Real.exp_neg, inv_inv], inv_pow]
        ring
      have hm : h1 w0 ≤ h1 w := hmin (ball_subset_closedBall hw)
      have hq : 0 ≤ ‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)) := by positivity
      calc h1 w0 * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)))
          ≤ h1 w * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ))) := mul_le_mul_of_nonneg_right hm hq
        _ = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) := by
            rw [show densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) = ‖P (cpt X x1 w)‖ ^ 2 * (densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
              S⁻¹ ^ (nd X)) by ring, hid]
            ring
    · have hN' : n2 = 0 := hN.symm
      rw [hN', Real.zero_rpow (by have := Xa.n_ge; simp; omega), mul_zero, ENNReal.ofReal_zero,
        mul_zero]
      exact zero_le
  calc ENNReal.ofReal (h1 w0) * ∫⁻ w in ball (0 : V (nd X)) ρ1,
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ)))
      = ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ w in OmF X x1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) :=
        lintegral_mono_set (ball_subset_closedBall.trans hcb)
    _ = _ := (muF_lintegral X x1 _).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem vanish_other (hV : VanishAtSStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0)
    (bb : ℝ) (hbb : 0 ≤ bb) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (b0 : Frame X.Ψ r)
    (hb0 : b0 ∈ Bor X.Ψ r) (j : Fin Fl.δ) (hx : Fl.xs j = rmul x0 b0) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hBE : IsBEq X Xa.Fp P) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (j' : Fin Fl.δ) (hne : γ ≠ 1 ∨ j' ≠ j) :
    P (lact γ (Fl.xs j')) = 0 := by
  have hw0sec : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hssec : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hy : lact γ (Fl.xs j') ∈ X.dom := OntoS.dom_lact X hγ (Fl.xs_mem j')
  obtain ⟨x1, ho1, b1, hb1, hyeq⟩ := hO r X _ hy
  have hx1dom : x1 ∈ X.dom := orth_mem_dom X x1 ho1

  have hs1 : ∀ k, Fl.s k x1 = 0 := by
    intro k
    have h0 : Fl.s k (lact γ (Fl.xs j')) = 0 :=
      (Fl.S_eq _ hy).2 ⟨j', γ, hγ, idF X, idF_mem X, by rw [rmul_idF]⟩ k
    rw [hyeq, (hssec k).2.1 x1 hx1dom b1 hb1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (bchar_ne_zero X hb1 _)
  have hw1 : Fl.w0 x1 ≠ 0 := by
    intro h
    have h1 : Fl.w0 (lact γ (Fl.xs j')) = X.χ Xa.L γ * Fl.w0 (Fl.xs j') :=
      hw0sec.2.2 γ hγ _ (Fl.xs_mem j')
    rw [hyeq, hw0sec.2.1 x1 hx1dom b1 hb1, h, mul_zero] at h1
    exact mul_ne_zero (chi_ne X hγ) (Fl.w0_ne j') h1.symm
  have hx0dom : x0 ∈ X.dom := orth_mem_dom X x0 ho
  have hx0d : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ => (hx0dom τ).1
  have hx1d : ∀ τ, (mat x1 τ).det ≠ 0 := fun τ => (hx1dom τ).1
  have hx1av := avoid_base X Xa Fl j j' hγ hne x0 b0 hb0 hx x1 b1 hb1 hyeq ε hball hiso hs1
  obtain ⟨Nb, hNb, hNbav⟩ :=
    nbhd_avoid X x0 hx0d (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hx1av hx1d
  have hOm : IsOpen (OmF X x1) := (isOpen_dom X).preimage (cpt_diff X x1).continuous
  have hS : OmF X x1 ∩ cpt X x1 ⁻¹' Nb ∈ 𝓝 (0 : V (nd X)) := by
    refine Filter.inter_mem (hOm.mem_nhds (zero_mem_OmF X x1 ho1)) ?_
    apply (cpt_diff X x1).continuous.continuousAt.preimage_mem_nhds
    rw [cpt_zero X x1]
    exact hNb
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hS
  have hρ : 0 < δ / 2 := half_pos hδ
  have hcbδ : closedBall (0 : V (nd X)) (δ / 2) ⊆ ball 0 δ :=
    Metric.closedBall_subset_ball (half_lt_self hδ)
  have hcb : closedBall (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 := fun w hw => (hδsub (hcbδ hw)).1
  have hbO : ball (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 :=
    fun w hw => hcb (Metric.ball_subset_closedBall hw)
  have hbN : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nb :=
    fun w hw => (hδsub (hcbδ (Metric.ball_subset_closedBall hw))).2

  obtain ⟨Δ, zOf, bOf, hΔ, -, hzOf, -, hdec, hlast⟩ := hLU r X x1 ho1
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nset X Δ zOf (δ / 2) := by
    intro w hw
    obtain ⟨hΔw, hzw, -⟩ := hlast w (hbO hw) (idF X) (idF_mem X)
    rw [rmul_idF] at hΔw hzw
    show (cpt X x1 w ∈ X.dom ∧ Δ (cpt X x1 w) ≠ 0) ∧ zOf (cpt X x1 w) ∈ ball (0 : V (nd X)) (δ / 2)
    exact ⟨⟨hbO hw, hΔw⟩, by rw [hzw]; exact hw⟩
  have hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ Nset X Δ zOf (δ / 2) →
      z ∉ closedBall (0 : V (nd X)) (2 * ε) := by
    intro z _ hzN hzB
    generalize hxz : cpt X x0 z = x at hzN
    have hzN' : (x ∈ X.dom ∧ Δ x ≠ 0) ∧ zOf x ∈ ball (0 : V (nd X)) (δ / 2) := hzN
    obtain ⟨⟨hxd, hxΔ⟩, hxb⟩ := hzN'
    obtain ⟨-, hbB, hxeq⟩ := hdec x hxd hxΔ
    apply hNbav _ (hbN _ hxb) z hzB (binv X (bOf x)) (binv_mem X hbB)
    calc cpt X x1 (zOf x) = rmul (rmul (cpt X x1 (zOf x)) (bOf x)) (binv X (bOf x)) :=
          (rmul_binv X _ hbB).symm
      _ = rmul x (binv X (bOf x)) := by rw [← hxeq]
      _ = rmul (cpt X x0 z) (binv X (bOf x)) := by rw [hxz]
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hNopen : IsOpen (Nset X Δ zOf (δ / 2)) :=
    hzOf.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hmeas : Measurable ((Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s)) :=
    (gφ_meas X P hBE.1.continuousOn Xa.Fp Xa.L Fl.s fun k => (hssec k).1.continuousOn).indicator
      hNopen.measurableSet
  have hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) (rmul x b) =
        (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) x := by
    classical
    intro x hx b hb
    have hiff := Nset_sat X x1 hdec hlast (δ / 2) hx hb
    by_cases hxN : x ∈ Nset X Δ zOf (δ / 2)
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hiff.2 hxN), if_pos hxN,
        gφ_rmul X hR hBE hssec hx hb]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hxN (hiff.1 h)), if_neg hxN]

  obtain ⟨c1, hc1, hc1le⟩ := rhs_bound X x1 Xa Fl P (Nset X Δ zOf (δ / 2)) (δ / 2) hρ hcb hN1
  have hfin := lhs_finite X x0 ho Xa Fl ψ C0 hψb bb hbb ε hε hnull F hI P hPF
    (Nset X Δ zOf (δ / 2)) hN2
  have heq := hM r X x1 x0 ho1 ho _ hmeas hinv
  have hlt := hc1le.trans_lt (heq.trans_lt hfin)
  have hfinI := ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ENNReal.ofReal_pos.2 hc1).ne'
  have hdet := etale_transfer X hLU hw0sec hssec (Fl.xs_mem j') (Fl.coord j') hγ (idF_mem X) ho1
    hb1 (by rw [rmul_idF]; exact hyeq) hw1
  have hnd : 0 < nd X := by have := Xa.n_ge; omega
  have hP1 : P x1 = 0 :=
    hV r X x1 hnd ho1 hx1dom P Fl.w0 Fl.s (δ / 2) hρ ((comp_cpt_diffOn X hBE.1 x1).mono hbO)
      (fun k => (comp_cpt_diffOn X (hssec k).1 x1).mono hbO)
      ((comp_cpt_diffOn X hw0sec.1 x1).mono hbO) hw1 hs1 hdet hfinI
  rw [hyeq, hBE.2 x1 hx1dom b1 hb1, hP1, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi_of (hE : ExtFStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hV : VanishAtSStatement (E := E)) (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E))
    (hC : OmFConnStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (hLa : NfacLactStatement (E := E)) : KronHolPsiStatement (E := E) := by
  intro r X Xa Fl _hPD ψ hψ hψs hψb hbm0 hstr0 hLnn j
  obtain ⟨bb, m, hbb4, hbm, hmar⟩ := hbm0
  obtain ⟨η, hη, hstr⟩ := hstr0
  obtain ⟨C0, hC0⟩ := hψb

  obtain ⟨x0, ho, b0, hb0, hx⟩ := hO r X (Fl.xs j) (Fl.xs_mem j)
  have hbbpos : 0 < bb := lt_of_le_of_lt (by positivity) hbb4

  obtain ⟨ε, hε, hball, hiso, hnull, F, hFd, hI⟩ :=
    coord_step (X := X) hLU hC Xa Fl ψ x0 ho (hψs x0 ho) bb m hbbpos hbm (hmar x0 ho) η hη (hstr x0 ho)
      (hLnn x0 ho) j b0 hb0 hx
  have hint := integ_step (X := X) x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball hnull F hI

  obtain ⟨P, hBE, hPF⟩ :=
    hE r X x0 ho Xa.Fp F hFd (extF_hyp (X := X) x0 ho Xa.Fp ψ C0 hC0 bb hbbpos.le F hint)
  obtain ⟨hw, hs0, hdet⟩ := coord_data (X := X) hLU Xa Fl j x0 ho b0 hb0 hx
  have hP1 : P x0 = 1 :=
    value_base (X := X) hV x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball F hFd hI P hPF hw hs0 hdet
  have hMW := metricW_of hR hLa hO hLU X Xa.Fp ψ hψ hψs ⟨C0, hC0⟩
  refine ⟨x0, Wpsi X Xa.Fp ψ, bb, F, P, 1, ho, hMW.1, hMW.2, ?_, hbb4, hFd,
    inAt_of (X := X) x0 Xa.Fp ψ bb F hint, hBE, hPF, X.Γ.one_mem, ?_, ?_⟩
  · intro x hx'
    simp [Wpsi, hx']
  · rw [lact_one (X := X), hx, hBE.2 x0 (orth_mem_dom (X := X) x0 ho) b0 hb0, hP1, mul_one]
    exact bchar_ne_zero (X := X) hb0 Xa.Fp
  · intro γ hγ j' hne
    exact vanish_other (X := X) hV hM hO hLU hR Xa Fl ψ C0 hC0 bb hbbpos.le x0 ho b0 hb0 j hx ε hε hball
      hiso hnull F hI P hBE hPF hγ j' hne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi_of_frameMeas (hF : FrameMeasStatement (E := E)) : KronHolPsiStatement (E := E) :=
  IW.kronHolPsi_of (extF_of lu_holds hF) measInv_holds vanishAtS_holds ortho_holds lu_holds
    OmFConnStatement_holds normFactor_rightBorel_holds normFactor_leftAction_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
