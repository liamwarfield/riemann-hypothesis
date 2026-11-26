module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPf
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem exists_s_ne {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) :
    ∃ k0 : Fin (nd X), ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ k, ∀ x ∈ X.dom, Fl.s k x = 0 := fun k =>
    bigCell_of lu_holds r X x0 hx0 Xa.L (Fl.s k) ⟨(Fl.s_van k).1.1.1.1, (Fl.s_van k).1.1.1.2.1⟩ (hcon k)
  have hx0d := IW.orth_mem_dom X x0 hx0
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0d).1 (fun k => hall k x0 hx0d)
  have hc := Fl.coord j
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X _).mem_nhds h0] with z hz
    simp [hall _ _ hz]
    rfl
  rw [hev.fderiv_eq, fderiv_const_apply] at hc
  apply hc
  have h2 := Xa.n_ge
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact zero_pow (by omega)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def Gf (Xa : ArchInM X) (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (‖g x‖ ^ 2) * WSk X Xa Fl x

theorem Gf_meas (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ} (hg : ContinuousOn g X.dom) :
    Measurable (Gf Xa Fl g) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise g 0) := hg.measurable_piecewise continuousOn_const hm
  have h2 := ((h1.norm.pow_const 2).ennreal_ofReal).mul (WSk_meas Xa Fl)
  convert h2 using 1
  funext x
  by_cases hx : x ∈ X.dom
  · simp [Gf, hx]
  · simp [Gf, WSk, hx]

theorem Gf_rmul (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ}
    (hg : X.IsSec (Xa.Fp + Xa.T • Xa.L) g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Gf Xa Fl g (rmul x b) = Gf Xa Fl g x := by
  have hq : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (IW.bchar_ne_zero X hb _)) 2
  have hq0 : ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq
  unfold Gf
  rw [(WSk_metric Xa Fl).2.1 x hx b hb, hg.2.1 x hx b hb, norm_mul, mul_pow,
    ENNReal.ofReal_mul hq.le, div_eq_mul_inv]
  calc ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) * ENNReal.ofReal (‖g x‖ ^ 2) *
        (WSk X Xa Fl x * (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2))⁻¹)
      = ENNReal.ofReal (‖g x‖ ^ 2) * WSk X Xa Fl x * (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) *
        (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2))⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hq0 ENNReal.ofReal_ne_top, mul_one]

theorem Gf_lact (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ}
    (hg : X.IsSec (Xa.Fp + Xa.T • Xa.L) g) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : Gf Xa Fl g (lact γ x) = Gf Xa Fl g x := by
  unfold Gf
  rw [(WSk_metric Xa Fl).2.2 γ hγ x hx, hg.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X _ hγ, one_mul]

private lemma nfac_pos_of_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by
  have hd : ∀ τ j, dmin X.Gm x τ j ≠ 0 := by
    intro τ j h
    have h' := (hx τ).2 j
    rw [h] at h'
    simp at h'
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

private lemma nfac_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la L : Wt X.Ψ r) (T : ℕ) :
    X.nfac (la + T • L) x = X.nfac la x * X.nfac L x ^ T := by
  unfold Data.nfac
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : ∀ j, dmin X.Gm x τ j ≠ 0 := by
    intro j h
    have h' := (hx τ).2 j
    rw [h] at h'
    simp at h'
  have hpos : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    norm_pos_iff.mpr (div_ne_zero (hd _) (hd _))
  have he : -(((la + T • L) τ i : ℤ) : ℝ) / 2 =
      -((la τ i : ℤ) : ℝ) / 2 + -((L τ i : ℤ) : ℝ) / 2 * (T : ℝ) := by
    have h1 : ((la + T • L) τ i : ℤ) = la τ i + T • L τ i := rfl
    rw [h1, nsmul_eq_mul]
    push_cast
    ring
  rw [he, Real.rpow_add hpos, Real.rpow_mul hpos.le, Real.rpow_natCast]

theorem Gf_le_off (Xa : ArchInM X) (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (K : ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hK : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) :
    Gf Xa Fl g x ≤ ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) *
      ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) := by
  unfold Gf WSk
  rw [if_pos hx]
  have hnn : 0 < X.nfac (Xa.Fp + Xa.T • Xa.L) x := nfac_pos_of_mem_dom hx _
  have hexp : Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) = X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2 := by
    unfold phla
    rw [show -(-2 * Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x)) =
      Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) + Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) by ring,
      Real.exp_add, Real.exp_log hnn]
    ring
  have hp : X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 = ‖g x‖ ^ 2 * X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2 := by
    show (‖g x‖ * X.nfac (Xa.Fp + Xa.T • Xa.L) x) ^ 2 = _
    ring
  have hW : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    have hk' : 0 < X.pnorm Xa.L (Xa.w k) x ^ 2 := by
      have : 0 < X.pnorm Xa.L (Xa.w k) x := mul_pos (norm_pos_iff.mpr hk) (nfac_pos_of_mem_dom hx _)
      positivity
    exact lt_of_lt_of_le hk' (Finset.single_le_sum (f := fun j => X.pnorm Xa.L (Xa.w j) x ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k))
  have hS0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hexp, hp, ENNReal.ofReal_rpow_of_pos hW]
  set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWd
  set S := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSd
  set n := X.nfac (Xa.Fp + Xa.T • Xa.L) x with hnd
  have hS : 0 < S := by
    rcases hS0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hK
      linarith
  have hT : (1 / 2 : ℝ) ≤ (Xa.T : ℝ) := by
    have h1 : 1 ≤ Xa.T := by
      have := Xa.T_ge
      have := Xa.n_ge
      nlinarith
    have : (1 : ℝ) ≤ (Xa.T : ℝ) := by exact_mod_cast h1
    linarith
  have hratio : 1 / (max K 0 + 1) ≤ S / W := by
    rw [div_le_div_iff₀ (by positivity) hW]
    have : K * S ≤ max K 0 * S := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    nlinarith
  have hA : ENNReal.ofReal (S / W) ^ (-((Xa.T : ℝ) - 1 / 2)) ≤
      ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) :=
    by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) (by linarith))
  rw [ENNReal.ofReal_mul (p := ‖g x‖ ^ 2 * n ^ 2) (by positivity),
    ENNReal.ofReal_mul (p := ‖g x‖ ^ 2) (by positivity)]
  have key := mul_le_mul_of_nonneg_left
    (a := ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (W ^ (-(Xa.T : ℝ)))) hA
    (by positivity)
  calc _ = ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (W ^ (-(Xa.T : ℝ))) *
        ENNReal.ofReal (S / W) ^ (-((Xa.T : ℝ) - 1 / 2)) := by ring
    _ ≤ _ := key
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Metric
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem s_not_ev_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) :
    ∃ k, ¬ (fun z => Fl.s k (cpt X (Fl.xs j) z)) =ᶠ[𝓝 (0 : V (nd X))] 0 := by
  by_contra hcon
  push_neg at hcon
  have hc := Fl.coord j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Filter.eventually_all.2 hcon] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]
    rfl
  rw [hev.fderiv_eq, fderiv_const_apply] at hc
  apply hc
  have h2 := Xa.n_ge
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact zero_pow (by omega)

theorem T_ge_n (Xa : ArchInM X) : nd X ≤ Xa.T := by
  have h1 := Xa.T_ge
  have h2 : nd X ≤ nd X ^ 2 := Nat.le_self_pow two_ne_zero _
  exact h2.trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h1)

theorem exp_neg_PsK (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    Real.exp (-PsK Xa Fl x) = Real.exp (-phla X Xa.Fp x) * (∑ k, Complex.normSq (Xa.w k x)) ^ (-(1 / 2 : ℝ)) *
      (∑ k, Complex.normSq (Fl.s k x)) ^ (-((Xa.T : ℝ) - 1 / 2)) := by
  have hn : 0 < X.nfac Xa.L x := nfac_pos_of_mem_dom hx Xa.L
  have hnF : 0 < X.nfac Xa.Fp x := nfac_pos_of_mem_dom hx Xa.Fp
  have hp : ∀ P : Frame X.Ψ r → ℂ,
      X.pnorm Xa.L P x ^ 2 = X.nfac Xa.L x ^ 2 * Complex.normSq (P x) := by
    intro P
    show (‖P x‖ * X.nfac Xa.L x) ^ 2 = _
    rw [Complex.normSq_eq_norm_sq]; ring
  have hW : 0 < ∑ k, Complex.normSq (Xa.w k x) := by
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hk)
      (Finset.single_le_sum (f := fun j => Complex.normSq (Xa.w j x))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ k))
  have sw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Xa.w k x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hp _
  have ss : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Fl.s k x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hp _
  have hnf : X.nfac (Xa.Fp + Xa.T • Xa.L) x = X.nfac Xa.Fp x * X.nfac Xa.L x ^ Xa.T :=
    nfac_add_nsmul hx _ _ _
  unfold PsK phla
  rw [sw, ss, hnf, mul_div_mul_left _ _ (pow_pos hn 2).ne', Real.rpow_def_of_pos hW,
    Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_mul (pow_pos hn 2).ne' hW.ne', Real.log_div hs.ne' hW.ne',
    Real.log_mul hnF.ne' (pow_pos hn _).ne']
  simp only [Real.log_pow]
  push_cast
  ring

theorem ball_finite {Xa : ArchInM X} (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (j : Fin Fl.δ)
    {ρV ρ : ℝ} (hρ : 0 < ρ) (hρV : ρ ≤ ρV)
    (hV : ∫⁻ z in ball (0 : V (nd X)) ρV, ENNReal.ofReal (‖g (cpt X (Fl.xs j) z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X (Fl.xs j) z)‖ ^ 2) ^ (-(((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2))) < ⊤)
    (hsub : closedBall (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j)) :
    ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (cpt X (Fl.xs j) z) < ⊤ := by
  set c := cpt X (Fl.xs j) with hc
  have hex : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2 = (Xa.T : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (T_ge_n Xa)]; ring
  rw [hex] at hV
  obtain ⟨k, hk⟩ := s_not_ev_zero Fl j
  have hbO : ball (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j) := ball_subset_closedBall.trans hsub
  have hF : DifferentiableOn ℂ (fun z => Fl.s k (c z)) (ball (0 : V (nd X)) ρ) :=
    (IW.comp_cpt_diffOn X (s_diffOn Fl k) (Fl.xs j)).mono hbO
  have hnull := HE.zeros_null isOpen_ball hF
    (HE.hgn_of isOpen_ball (convex_ball _ _).isPreconnected hF (mem_ball_self hρ) hk)

  have hQc : ContinuousOn (fun z => Real.exp (-phla X Xa.Fp (c z)) *
      (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ))) (closedBall (0 : V (nd X)) ρ) := by
    intro z hz
    have hzO := hsub hz
    have h1 := (IW.phla_cpt_cdAt X (Fl.xs j) hzO Xa.Fp).continuousAt
    have h2 := (sumSq_cdAt (ExF.isOpen_OmF X (Fl.xs j))
      (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) (Fl.xs j)) hzO).continuousAt
    exact ((h1.neg.rexp).mul (h2.rpow_const (Or.inl (sumw_pos Xa hzO).ne'))).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ).exists_bound_of_continuousOn hQc
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (mem_closedBall_self hρ.le))
  have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : V (nd X)) ρ)), Gf Xa Fl g (c z) ≤
      ENNReal.ofReal C * ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzb
    have hFz : Fl.s k (c z) ≠ 0 := fun h => hz ⟨hzb, h⟩
    have hzO := hbO hzb
    have hSp := sums_pos Fl hFz
    have hQ := hC z (ball_subset_closedBall hzb)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _))] at hQ
    unfold Gf
    rw [WSk_eq_exp Xa Fl hzO hSp, exp_neg_PsK Xa Fl hzO hSp, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul hC0]
    apply ENNReal.ofReal_le_ofReal
    simp only [Complex.sq_norm]
    have hA : 0 ≤ Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2)) :=
      mul_nonneg (Complex.normSq_nonneg _) (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _)
    calc Complex.normSq (g (c z)) * (Real.exp (-phla X Xa.Fp (c z)) * (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ)) *
          (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2)))
        = (Real.exp (-phla X Xa.Fp (c z)) * (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ))) *
          (Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2))) := by ring
      _ ≤ C * (Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        mul_le_mul_of_nonneg_right hQ hA
  calc ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (c z)
      ≤ ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal C * ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) := lintegral_mono_ae hae
    _ = ENNReal.ofReal C * ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z in ball (0 : V (nd X)) ρV, ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        mul_le_mul' le_rfl (lintegral_mono_set (ball_subset_ball hρV))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Metric
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def SatB (X : Data E r) (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)}

theorem satB_sat (x1 : Frame X.Ψ r) (ρ : ℝ) {x : Frame X.Ψ r} (hx : x ∈ SatB X x1 ρ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : lact γ (rmul x b) ∈ SatB X x1 ρ := by
  obtain ⟨γ', hγ', b', hb', z', hz', rfl⟩ := hx
  refine ⟨γ * γ', X.Γ.mul_mem hγ hγ', rmul b' b,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem (X := X) hb' hb, z', hz', ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_rmul, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_lact,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc]

theorem mem_satB_self (x1 : Frame X.Ψ r) {ρ : ℝ} (hρ : 0 < ρ) : x1 ∈ SatB X x1 ρ := by
  have hn : nmat X 0 = fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) := by
    funext τ a c
    simp only [nmat]
    split_ifs with h1 h2
    · rw [Matrix.one_apply_ne (ne_of_lt h1).symm]
      first | rfl | simp | exact PiLp.zero_apply _ _
    · subst h2; exact (Matrix.one_apply_eq a).symm
    · exact (Matrix.one_apply_ne h2).symm
  refine ⟨1, X.Γ.one_mem, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), ?_, 0, Metric.mem_ball_self hρ, ?_⟩
  · intro τ
    refine ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
      exact Matrix.one_apply_ne (ne_of_lt hca).symm
  · funext τ a c
    simp [lact, rmul, mat, cpt, hn]
    change x1 τ a c = ((Matrix.of (x1 τ) * (1 : Matrix (Fin r) (Fin r) ℂ)) *
      (1 : Matrix (Fin r) (Fin r) ℂ)) a c
    rw [Matrix.mul_one, Matrix.mul_one]
    rfl

theorem rpow_ofReal_ne_top {a : ℝ} (ha : 0 < a) (y : ℝ) : ENNReal.ofReal a ^ y ≠ ⊤ := by
  rw [ENNReal.ofReal_rpow_of_pos ha]
  exact ENNReal.ofReal_ne_top

theorem inFF_of (hLU : LocalUnfoldBStatement (E := E)) {Xa : ArchInM X} (Fl : FlatM X Xa) (hPD : PropDisc X)
    (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) (FF : Set (V (nd X))) (hFF : IsFundSet X x0 FF)
    (g : Frame X.Ψ r → ℂ) (hg : g ∈ X.SS (Xa.Fp + Xa.T • Xa.L))
    (hint : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤)
    (hv : VanS X Fl.xs Fl.s (Xa.T - nd X) g) : InFF X x0 (WSk X Xa Fl) FF g := by
  have hsec : X.IsSec (Xa.Fp + Xa.T • Xa.L) g := hg.1.1
  have hGm := Gf_meas Xa Fl hsec.1.continuousOn
  have key : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧ IsOpen (SatB X (Fl.xs j) ρ) ∧
      ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ,
        cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)}, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    intro j
    obtain ⟨ρV, hρV, hV⟩ := hv j
    obtain ⟨ρ0, hρ0, hL⟩ := hLU r X x0 hx0 hPD FF hFF (Fl.xs j) (Fl.xs_mem j)
    have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [IW.cpt_zero]
      exact Fl.xs_mem j
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (ExF.isOpen_OmF X (Fl.xs j)) 0 h0
    set ρ := min (min ρV ρ0) (ε / 2) with hρdef
    have hρ : 0 < ρ := lt_min (lt_min hρV hρ0) (by linarith)
    have hρV' : ρ ≤ ρV := (min_le_left _ _).trans (min_le_left _ _)
    have hρ0' : ρ ≤ ρ0 := (min_le_left _ _).trans (min_le_right _ _)
    have hcl : closedBall (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j) :=
      (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hεsub
    obtain ⟨hop, K, hK, hb⟩ := hL ρ hρ hρ0'
    refine ⟨ρ, hρ, hop, ?_⟩
    calc _ ≤ K * ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (cpt X (Fl.xs j) z) :=
          hb _ hGm (fun x hx b hb => Gf_rmul Xa Fl hsec hx hb) (fun γ hγ x hx => Gf_lact Xa Fl hsec hγ hx)
      _ < ⊤ := ENNReal.mul_lt_top hK (ball_finite Fl g j hρ hρV' hV hcl)
  choose ρ hρ hop hfin using key
  set U := ⋃ j, SatB X (Fl.xs j) (ρ j) with hUdef
  have hU : IsOpen U := isOpen_iUnion hop
  have hxs : ∀ j, Fl.xs j ∈ U := fun j => Set.mem_iUnion.2 ⟨j, mem_satB_self _ (hρ j)⟩
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨j, satB_sat _ _ hj hγ hb⟩
  obtain ⟨K, hK⟩ := Fl.family_le_coords U hU hxs hsat
  set P := {z : V (nd X) | cpt X x0 z ∈ U} with hPdef
  have hPm : MeasurableSet P := ((IW.cpt_diff X x0).continuous.isOpen_preimage _ hU).measurableSet
  set C := ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) with hCdef
  have hC : C ≠ ⊤ := rpow_ofReal_ne_top (by positivity) _
  have hoff : ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    calc ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
        ≤ ∫⁻ z in FF \ P, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 := by
          refine setLIntegral_mono' (hFF.1.diff hPm) fun z hz => ?_
          have hzd : cpt X x0 z ∈ X.dom := hFF.2.1 hz.1
          exact Gf_le_off Xa Fl g K hzd (hK _ hzd hz.2)
      _ ≤ ∫⁻ z in FF, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_mono_set Set.diff_subset
      _ = C * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_const_mul' _ _ hC
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hint
  have hcover : FF ⊆ (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)} := by
    intro z hz
    by_cases hzP : z ∈ P
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hzP
      exact Or.inr (Set.mem_iUnion.2 ⟨j, hz, hj⟩)
    · exact Or.inl ⟨hz, hzP⟩
  show ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤
  calc ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
      ≤ ∫⁻ z in (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_mono_set hcover
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∫⁻ z in ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_union_le _ _ _
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∑' j, ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := add_le_add le_rfl (lintegral_iUnion_le _ _)
    _ < ⊤ := by
      rw [tsum_fintype]
      exact ENNReal.add_lt_top.2 ⟨hoff, ENNReal.sum_lt_top.2 fun j _ => hfin j⟩

theorem ontoWeight_of (hLU : LocalUnfoldBStatement (E := E)) : OntoWeightStatement (E := E) := by
  intro r X Xa Fl hPD _ bb m _ _ hlevi _ x0 hx0 FF hFF
  obtain ⟨k0, z0, hz0, hs0⟩ := exists_s_ne Fl x0 hx0
  refine ⟨PsK Xa Fl, fun z => Fl.s k0 (cpt X x0 z), WSk_metric Xa Fl, WSk_lower Xa Fl,
    IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0, ⟨z0, hz0, hs0⟩, fun z hz => ?_, fun z hz hg1 => ?_,
    fun z hz hg1 ξ => ?_, fun g hg hint hv => ?_⟩
  · exact (PsK_cpt_cdAt Fl x0 k0 hz).contDiffWithinAt
  · exact WSk_eq_exp Xa Fl hz (sums_pos Fl hg1)
  · exact PsK_levi Fl x0 k0 m (hlevi x0 hx0) ⟨hz, hg1⟩ ξ
  · exact inFF_of hLU Fl hPD x0 hx0 FF hFF g hg hint hv

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

theorem densF_meas {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : Measurable fun w => ENNReal.ofReal (densF X x w) := by
  have hm : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ :=
    fun τ i => (OntoB.cd_dmin (X := X) (x0 := x) (τ := τ) (i := i.castSucc)).continuous.norm.measurable
  have hf : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ ^ (-2 : ℤ) := by
    intro τ i
    simp only [zpow_neg, zpow_ofNat]
    exact ((hm τ i).pow_const 2).inv
  have hp : Measurable fun w => densF X x w := by
    unfold densF
    exact Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => hf τ i
  exact ENNReal.measurable_ofReal.comp hp

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := by
  intro r X x0 ho hPD FF hFF x1 hx1
  classical
  obtain ⟨x1', ho', b1, hb1, rfl⟩ := ortho_holds r X x1 hx1
  obtain ⟨D⟩ := ExtFPf.luData_of hLU X x1' ho'
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  obtain ⟨ρ1, hρ1, hball1⟩ := exists_ball X b1 D ho' hb1
  obtain ⟨ρ2, hρ2, hball2⟩ := Metric.isOpen_iff.mp (ExF.isOpen_OmF X x1') 0 (IW.zero_mem_OmF X x1' ho')
  set ρ0 : ℝ := min ρ1 ρ2 / 2 with hρ0def
  have hρ0 : 0 < ρ0 := by positivity
  have hρ01 : ρ0 < ρ1 := by have := min_le_left ρ1 ρ2; linarith
  have hρ02 : ρ0 < ρ2 := by have := min_le_right ρ1 ρ2; linarith
  have hcl : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D := fun z hz =>
    hball1 z (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ01))
  have hclO : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ OmF X x1' := fun z hz =>
    hball2 (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ02))
  obtain ⟨Kj, hKj⟩ := jac_bound X b1 D hcl
  obtain ⟨Kd, hKd⟩ := dens_bound X b1 D hcl
  refine ⟨ρ0, hρ0, fun ρ hρ hρle => ?_⟩
  have hbcl : Metric.ball (0 : V (nd X)) ρ ⊆ Metric.closedBall 0 ρ0 := fun z hz =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρle hz)
  have hbU : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D := hbcl.trans hcl
  have hbO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1' := hbcl.trans hclO
  have hopen := isOpen_sat D ho' hb1 hbO
  refine ⟨hopen, ENNReal.ofReal (max Kd 0 * max Kj 0), ENNReal.ofReal_lt_top, fun G hG hGB hGΓ => ?_⟩
  set x1 := rmul x1' b1 with hx1def
  set T := Tset X x1 ρ with hTdef
  have hT : MeasurableSet T := meas_Tset X b1 D ho' hbU hx1
  have hTeq : T = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := Tset_eq X b1 D hbU
  have hTB : ∀ y b, b ∈ Bor X.Ψ r → (rmul y b ∈ T ↔ y ∈ T) := fun y b hb => by
    rw [hTeq]; exact KU.rmul_mem_S X hb
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1').measurable
  have hae0 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  set Sat : Set (V (nd X)) := {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
    cpt X x0 z = lact γ (rmul (cpt X x1 z') b)} with hSatdef
  have hSat : MeasurableSet Sat := (hopen.preimage (KU.cont_cpt X x0)).measurableSet

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * T.indicator 1 (lact γ.1⁻¹ y) * G y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    ((measurable_one.indicator hS).mul ((measurable_one.indicator hT).comp (KU.cont_lact X γ.1⁻¹).measurable)).mul hG
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x hx b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : lact γ.1⁻¹ (rmul x b) ∈ T ↔ lact γ.1⁻¹ x ∈ T := by rw [KU.lact_rmul']; exact hTB _ _ hb
    simp only [H, Set.indicator_apply, e1, e2, hGB x hx b hb, Pi.one_apply]

  have stepA : ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine le_trans (setLIntegral_mono' (hFF.1.inter hSat) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
    obtain ⟨hzF, γ, hγ, b, hb, z', hz', he⟩ := hz
    have hT1 : lact γ⁻¹ (cpt X x0 z) ∈ T := by
      rw [he, KU.lact_lact, inv_mul_cancel, KU.lact_one]
      exact ⟨⟨z', b⟩, ⟨hz', hb⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    simp only [H, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hzF), Set.indicator_of_mem hT1,
      Pi.one_apply, one_mul]
  have stepB : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have stepC : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, (KU.Sset X x0 FF).indicator 1
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x0) ho (KU.isOrth_lact X γ.2 ho) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr_ae (hae0.mono fun z hz => ?_)
    show H γ (cpt X (lact γ.1 x0) z) = _
    rw [KU.cpt_lact]
    simp only [H, KU.lact_lact, inv_mul_cancel, KU.lact_one, hGΓ γ.1 γ.2 _ hz]
    ring
  have hIm : ∀ γ : X.Γ, Measurable fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x0)).measurable).mul
      (((measurable_one.indicator hT).comp hcpt0).mul (hG.comp hcpt0))
  have stepD : ∑' γ : X.Γ, ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (lact γ.1 (cpt X x0 z)) *
      (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 ≤
      ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hIm γ).aemeasurable]
    refine lintegral_mono fun z => ?_
    rw [ENNReal.tsum_mul_right]
    calc (∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x0 z))) *
          (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z))
        ≤ 1 * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := by
          gcongr; exact FSM.atMostOnce X ho hFF _
      _ = _ := one_mul _
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (fun y => T.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y * G y) (rmul x b) =
      (fun y => T.indicator 1 y * G y) x := by
    intro x hx b hb
    simp only [Set.indicator_apply, hTB x b hb, hGB x hx b hb, Pi.one_apply]
  have stepE : ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' :=
    hM r X x0 x1' ho ho' (fun y => T.indicator 1 y * G y) ((measurable_one.indicator hT).mul hG) hφB
  have hA : MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := meas_image X b1 D hbU hx1
  have stepF : ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' =
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun w => ?_
    have e : cpt X x1' w ∈ T ↔ w ∈ Φ X b1 D '' Metric.ball 0 ρ := by rw [hTeq]; exact KU.cpt_mem_S X ho' w
    by_cases hw : w ∈ Φ X b1 D '' Metric.ball 0 ρ
    · rw [Set.indicator_of_mem (e.mpr hw), Set.indicator_of_mem hw, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem (fun h => hw (e.mp h)), Set.indicator_of_notMem hw, zero_mul]
  have stepG : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' ≤
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) := by
    unfold muF
    rw [restrict_withDensity hA]
    refine (lintegral_withDensity_le_lintegral_mul _ (densF_meas X x1') _).trans ?_
    refine lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) (fun w => le_rfl)
  have hder : ∀ z ∈ Metric.ball (0 : V (nd X)) ρ,
      HasFDerivWithinAt (Φ X b1 D) (fderiv ℝ (Φ X b1 D) z) (Metric.ball 0 ρ) z := fun z hz =>
    ((((Φ_diffOn X b1 D) z (hbU hz)).differentiableAt ((isOpen_Uc X b1 D).mem_nhds (hbU hz))).restrictScalars ℝ
      ).hasFDerivAt.hasFDerivWithinAt
  have stepH : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) =
      ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hder
      ((Φ_injOn X b1 D hx1).mono hbU) _
  have stepI : ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) ≤
      ENNReal.ofReal (max Kd 0 * max Kj 0) * ∫⁻ z in Metric.ball 0 ρ, G (cpt X x1 z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨hΦO, hβ, e⟩ := split X b1 D (hbU hz)
    have hG1 : G (cpt X x1' (Φ X b1 D z)) = G (cpt X x1 z) := by
      rw [e, hGB _ (by exact hΦO) _ hβ]
    rw [hG1, ← mul_assoc]
    gcongr
    rw [ENNReal.ofReal_mul (le_max_right _ _), mul_comm]
    gcongr
    · exact (hKd z (hbcl hz)).trans (le_max_left _ _)
    · exact (hKj z (hbcl hz)).trans (le_max_left _ _)
  calc ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0
      ≤ _ := stepA
    _ = _ := stepB
    _ = _ := tsum_congr stepC
    _ ≤ _ := stepD
    _ = _ := stepE
    _ = _ := stepF
    _ ≤ _ := stepG
    _ = _ := stepH
    _ ≤ _ := stepI

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := LUB.localUnfoldB_of hLU

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem localUnfoldBStatement_holds : LocalUnfoldBStatement (E := E) :=
  LUB.localUnfoldB_of lu_holds

theorem ontoWeightStatement_holds : OntoWeightStatement (E := E) :=
  OW.ontoWeight_of localUnfoldBStatement_holds

theorem divCoreStatement_holds : DivCoreStatement (E := E) :=
  divCore_up_of ontoWeightStatement_holds upDiv_holds DivStartStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
