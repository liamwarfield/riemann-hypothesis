module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfN

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfD
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivD

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma dmin_ne_zero_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  have h' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  intro h0
  have := (h' τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

private lemma norm_dmin_succ_div_castSucc_pos_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
  norm_pos_iff.mpr (div_ne_zero (dmin_ne_zero_of_mem_dom X hx τ _) (dmin_ne_zero_of_mem_dom X hx τ _))

private lemma nfac_pos_of_mem_dom' (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    0 < X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx τ i) _

theorem phla_add (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    phla X (la + la') x = phla X la x + phla X la' x := by
  have hq := norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx
  have hmul : X.nfac (la + la') x = X.nfac la x * X.nfac la' x := by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (hq τ i)]
    congr 1
    simp only [Pi.add_apply, Int.cast_add]
    ring
  unfold phla
  rw [hmul, Real.log_mul (nfac_pos_of_mem_dom' X hx la).ne' (nfac_pos_of_mem_dom' X hx la').ne']
  ring

theorem phla_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (k : ℕ) (la : Wt X.Ψ r) :
    phla X (k • la) x = k * phla X la x := by
  have hq := norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx
  have hpow : X.nfac (k • la) x = X.nfac la x ^ k := by
    unfold Data.nfac
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hq τ i).le]
    congr 1
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    ring
  unfold phla
  rw [hpow, Real.log_pow]
  ring

theorem nfac_sq (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    X.nfac la x ^ 2 = Real.exp (-phla X la x) := by
  unfold phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (pow_pos (nfac_pos_of_mem_dom' X hx la) 2)]

theorem pnorm_sq (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) : X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * Real.exp (-phla X la x) := by
  have h : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  rw [h, mul_pow, nfac_sq X hx la]

variable (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (bb : ℝ)

noncomputable def Ss (z : V (nd X)) : ℝ := ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2

noncomputable def Sw (z : V (nd X)) : ℝ := ∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2

noncomputable def ph0 (z : V (nd X)) : ℝ :=
  phla X Xa.Fp (cpt X x0 z) - Real.log (densF X x0 z) + 1 / 2 * Real.log (Sw X Xa x0 z) -
    bb * rhF X x0 z

theorem Sw_pos {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < Sw X Xa x0 z := by
  obtain ⟨k, hk⟩ := Xa.w_nz _ hz
  unfold Sw
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hk) 2)
    (Finset.single_le_sum (f := fun j => ‖Xa.w j (cpt X x0 z)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ k))

theorem sumL_eq {z : V (nd X)} (hz : z ∈ OmF X x0) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ) :
    ∑ k, X.pnorm Xa.L (P k) (cpt X x0 z) ^ 2 =
      Real.exp (-phla X Xa.L (cpt X x0 z)) * ∑ k, ‖P k (cpt X x0 z)‖ ^ 2 := by
  have hx : cpt X x0 z ∈ X.dom := hz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pnorm_sq X hx]
  ring

private lemma mul_div_exp_mul_rpow_neg_eq_mul_rpow_mul_exp {D f A B T Ss Sw b : ℝ} (hD : 0 < D) (hSs : 0 < Ss) (hSw : 0 < Sw) :
    D * (f / Real.exp (-b) * (Real.exp (-(A + T * B)) * (Real.exp (-B) * Sw) ^ (-T) *
      (Real.exp (-B) * Ss / (Real.exp (-B) * Sw)) ^ (-(T - 1 / 2)))) =
      f * Ss ^ (-(T - 1 / 2)) * Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) := by
  have e1 : Real.exp (-B) * Ss / (Real.exp (-B) * Sw) = Ss / Sw :=
    mul_div_mul_left _ _ (Real.exp_pos _).ne'
  have h1 : Real.exp (-(A + T * B)) * Real.exp (-B * -T) = Real.exp (-A) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Sw ^ (-T) / Sw ^ (-(T - 1 / 2)) = Real.exp (-(1 / 2 * Real.log Sw)) := by
    rw [Real.rpow_def_of_pos hSw, Real.rpow_def_of_pos hSw, ← Real.exp_sub]
    congr 1
    ring
  have h3 : Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) =
      Real.exp (-A) * D * Real.exp (-(1 / 2 * Real.log Sw)) * Real.exp b := by
    rw [show -(A - Real.log D + 1 / 2 * Real.log Sw - b) =
        -A + Real.log D + -(1 / 2 * Real.log Sw) + b by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hD]
  have h4 : f / Real.exp (-b) = f * Real.exp b := by rw [Real.exp_neg, div_inv_eq_mul]
  rw [e1, Real.mul_rpow (Real.exp_pos _).le hSw.le, Real.div_rpow hSs.le hSw.le, ← Real.exp_mul, h4, h3]
  calc _ = D * f * Real.exp b * (Real.exp (-(A + T * B)) * Real.exp (-B * -T)) * Ss ^ (-(T - 1 / 2)) *
        (Sw ^ (-T) / Sw ^ (-(T - 1 / 2))) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem wSk_eq {z : V (nd X)} (hz : z ∈ OmF X x0) (hs : 0 < Ss X Xa Fl x0 z) (F : V (nd X) → ℂ) :
    ENNReal.ofReal (densF X x0 z) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * WSk X Xa Fl (cpt X x0 z)) =
      ENNReal.ofReal (‖F z‖ ^ 2 * Ss X Xa Fl x0 z ^ (-((Xa.T : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb z)) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hSw := Sw_pos X Xa x0 hz
  have hW := sumL_eq X Xa x0 hz Xa.w
  have hS := sumL_eq X Xa x0 hz Fl.s
  have hd : 0 < densF X x0 z := by
    unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.mpr (dmin_ne_zero_of_mem_dom X hx τ _)) _
  unfold Sw at hSw
  unfold Ss at hs
  rw [WSk, if_pos hx, phla_add X hx, phla_nsmul X hx, hW, hS]
  unfold kaF
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos (Real.exp_pos _) hSw),
    ENNReal.ofReal_rpow_of_pos (div_pos (mul_pos (Real.exp_pos _) hs) (mul_pos (Real.exp_pos _) hSw))]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd.le]
  congr 1
  unfold ph0 Ss Sw
  rw [neg_mul]
  exact mul_div_exp_mul_rpow_neg_eq_mul_rpow_mul_exp hd hs hSw

private lemma mul_div_exp_le_pow_mul_rpow_of_exp_neg_mul_le {D f A B n Ss Sw b Cs Cw : ℝ} (hD : 0 < D) (hSs : 0 < Ss) (hSw : 0 < Sw)
    (hn : 1 / 2 ≤ n) (hCs : Real.exp (-B) * Ss ≤ Cs) (hCw : Real.exp (-B) * Sw ≤ Cw) (hf : 0 ≤ f) :
    D * (f / Real.exp (-b) * Real.exp (-(A + n * B))) ≤
      Cs ^ (n - 1 / 2) * Cw ^ (1 / 2 : ℝ) *
        (f * Ss ^ (-(n - 1 / 2)) * Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b))) := by
  have hE := Real.exp_pos (-B)
  have hCs0 : 0 ≤ Cs := le_trans (mul_nonneg hE.le hSs.le) hCs
  have hCw0 : 0 ≤ Cw := le_trans (mul_nonneg hE.le hSw.le) hCw
  have hs' : Real.exp (-B) ≤ Cs / Ss := (le_div_iff₀ hSs).mpr hCs
  have hw' : Real.exp (-B) ≤ Cw / Sw := (le_div_iff₀ hSw).mpr hCw
  have hsplit : Real.exp (-(n * B)) = Real.exp (-B) ^ (n - 1 / 2) * Real.exp (-B) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hE, ← Real.exp_mul]
    congr 1
    ring
  have hk1 : Real.exp (-B) ^ (n - 1 / 2) ≤ Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) := by
    calc Real.exp (-B) ^ (n - 1 / 2) ≤ (Cs / Ss) ^ (n - 1 / 2) :=
          Real.rpow_le_rpow hE.le hs' (by linarith)
      _ = Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) := by
          rw [Real.div_rpow hCs0 hSs.le, Real.rpow_neg hSs.le, div_eq_mul_inv]
  have hk2 : Real.exp (-B) ^ (1 / 2 : ℝ) ≤ Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)) := by
    calc Real.exp (-B) ^ (1 / 2 : ℝ) ≤ (Cw / Sw) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hE.le hw' (by norm_num)
      _ = Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)) := by
          rw [Real.div_rpow hCw0 hSw.le, div_eq_mul_inv, ← Real.rpow_neg hSw.le,
            Real.rpow_def_of_pos hSw]
          congr 2
          ring
  have h3 : Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) =
      Real.exp (-A) * D * Real.exp (-(1 / 2 * Real.log Sw)) * Real.exp b := by
    rw [show -(A - Real.log D + 1 / 2 * Real.log Sw - b) =
        -A + Real.log D + -(1 / 2 * Real.log Sw) + b by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hD]
  have h4 : f / Real.exp (-b) = f * Real.exp b := by rw [Real.exp_neg, div_inv_eq_mul]
  have h5 : Real.exp (-(A + n * B)) = Real.exp (-A) * Real.exp (-(n * B)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h3, h4, h5, hsplit]
  have hprod := mul_le_mul hk1 hk2 (by positivity)
    (mul_nonneg (Real.rpow_nonneg hCs0 _) (Real.rpow_nonneg hSs.le _))
  have hc : 0 ≤ D * f * Real.exp b * Real.exp (-A) := by positivity
  calc _ = D * f * Real.exp b * Real.exp (-A) *
        (Real.exp (-B) ^ (n - 1 / 2) * Real.exp (-B) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ D * f * Real.exp b * Real.exp (-A) *
        (Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) *
          (Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)))) := mul_le_mul_of_nonneg_left hprod hc
    _ = _ := by ring

theorem weightedDensity_bound {z : V (nd X)} (hz : z ∈ OmF X x0) (hs : 0 < Ss X Xa Fl x0 z) (H : V (nd X) → ℂ)
    {Cs Cw : ℝ} (hCs : ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 ≤ Cs)
    (hCw : ∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2 ≤ Cw) (hn : (1 / 2 : ℝ) ≤ (nd X : ℝ)) :
    ENNReal.ofReal (densF X x0 z) * (ENNReal.ofReal (‖H z‖ ^ 2 / kaF X x0 bb z) * weightFunctionOnFrames X Xa (cpt X x0 z)) ≤
      ENNReal.ofReal (Cs ^ ((nd X : ℝ) - 1 / 2) * Cw ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (‖H z‖ ^ 2 * Ss X Xa Fl x0 z ^ (-((nd X : ℝ) - 1 / 2)) *
          Real.exp (-ph0 X Xa x0 bb z)) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hSw := Sw_pos X Xa x0 hz
  have hd : 0 < densF X x0 z := by
    unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.mpr (dmin_ne_zero_of_mem_dom X hx τ _)) _
  rw [sumL_eq X Xa x0 hz Fl.s] at hCs
  rw [sumL_eq X Xa x0 hz Xa.w] at hCw
  unfold Sw at hSw
  unfold Ss at hs
  have hCs0 : 0 < Cs := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hs) hCs
  have hCw0 : 0 < Cw := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hSw) hCw
  rw [weightFunctionOnFrames, phla_add X hx, phla_nsmul X hx]
  unfold kaF
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd.le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold ph0 Ss Sw
  rw [neg_mul]
  exact mul_div_exp_le_pow_mul_rpow_of_exp_neg_mul_le hd hs hSw hn hCs hCw (sq_nonneg _)

end UpDivD

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivE

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ)

theorem w_hol (k : Fin Xa.N) : DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) := by
  exact ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp (X := X) (x0 := x0) (Xa.w_van k).1.1.1.1

theorem Sw_eq : Sw X Xa x0 = fun z => sqNorm fun k => Xa.w k (cpt X x0 z) := by
  funext z
  simp [Sw, sqNorm, Complex.sq_norm]

theorem logSw_cdAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Sw X Xa x0 y)) z := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  have hk : ∀ k, ContDiffAt ℝ ∞ (fun y => ‖Xa.w k (cpt X x0 y)‖ ^ 2) z := by
    intro k
    have hd := w_hol X Xa x0 k
    have h1 : ContDiffAt ℂ ∞ (fun y => Xa.w k (cpt X x0 y)) z :=
      ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz
    exact (h1.restrict_scalars ℝ).norm_sq ℝ
  have hS : ContDiffAt ℝ ∞ (Sw X Xa x0) z := by
    have : Sw X Xa x0 = fun y => ∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2 := rfl
    rw [this]
    exact ContDiffAt.sum fun k _ => hk k
  have hpos : 0 < Sw X Xa x0 z := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    exact Finset.sum_pos' (fun k _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk0) 2⟩
  exact hS.log hpos.ne'

theorem plurisubharmonicWeight_smooth : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_cpt_cdAt (X := X) x0 hz Xa.Fp
  have h2 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.logDens_contDiffAt (X := X) (x0 := x0) hz
  have h3 := logSw_cdAt X Xa x0 hz
  have h4 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.rhF_contDiffAt (X := X) (x0 := x0) hz
  have h := ((h1.sub h2).add ((contDiffAt_const (c := (1 / 2 : ℝ))).mul h3)).sub
    ((contDiffAt_const (c := bb)).mul h4)
  exact h.contDiffWithinAt

theorem levi_logSw_nonneg {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((Real.log (Sw X Xa x0 y) : ℝ) : ℂ)) z ξ).re := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  simp only [Sw_eq X Xa x0]
  have hg : ∀ k, ContDiffAt ℂ 2 (fun y => Xa.w k (cpt X x0 y)) z := by
    intro k
    have hd := w_hol X Xa x0 k
    exact (ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz).of_le (by norm_cast)
  have hne : (fun k => Xa.w k (cpt X x0 z)) ≠ 0 := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    intro h
    exact hk0 (congrFun h k)
  have hl := leviLogNormSq (nd X) Xa.N (fun k y => Xa.w k (cpt X x0 y)) z ξ hg hne
  beta_reduce at hl
  rw [hl, Complex.ofReal_re]
  have hnn : ∀ {p : ℕ} (v : Fin p → ℂ), 0 ≤ sqNorm v := fun v =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  exact div_nonneg (hnn _) (hnn _)

theorem leviForm_weight_nonneg {m : ℝ} (hbm : bb ≤ m) (ho : IsOrth X x0)
    (hmar : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have hA := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hB := (OntoB.logDens_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hC := (logSw_cdAt X Xa x0 hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hD := (OntoB.rhF_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  set u : Fin 4 → V (nd X) → ℝ := ![fun w => phla X Xa.Fp (cpt X x0 w),
    fun w => -1 * Real.log (densF X x0 w) + 0, fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0,
    fun w => -bb * rhF X x0 w + 0] with hu
  have hu0 : u 0 = fun w => phla X Xa.Fp (cpt X x0 w) := rfl
  have hu1 : u 1 = fun w => -1 * Real.log (densF X x0 w) + 0 := rfl
  have hu2 : u 2 = fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0 := rfl
  have hu3 : u 3 = fun w => -bb * rhF X x0 w + 0 := rfl
  have hcu : ∀ i, ContDiffAt ℝ 2 (u i) z := by
    intro i; fin_cases i
    · show ContDiffAt ℝ 2 (u 0) z; rw [hu0]; exact hA
    · show ContDiffAt ℝ 2 (u 1) z; rw [hu1]; exact (contDiffAt_const.mul hB).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 2) z; rw [hu2]; exact (contDiffAt_const.mul hC).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 3) z; rw [hu3]; exact (contDiffAt_const.mul hD).add contDiffAt_const
  have he : (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) = fun w => ((∑ i, u i w : ℝ) : ℂ) := by
    funext w
    rw [Fin.sum_univ_four, hu0, hu1, hu2, hu3]
    unfold ph0
    push_cast; ring
  rw [he, leviV_ofReal_sum hcu, Complex.re_sum, Fin.sum_univ_four]
  have e1 := Y.leviV_const_mul (f := fun w => Real.log (densF X x0 w)) hB (-1) 0 ξ
  have e2 := Y.leviV_const_mul (f := fun w => Real.log (Sw X Xa x0 w)) hC (1 / 2) 0 ξ
  have e3 := Y.leviV_const_mul (f := fun w => rhF X x0 w) hD (-bb) 0 ξ
  rw [hu0, hu1, hu2, hu3, e1, e2, e3]
  have hm := hmar z hz ξ
  have hrh := ExF.levi_rhF_nonneg X x0 ho hz ξ
  have hlw := levi_logSw_nonneg X Xa x0 hz ξ
  unfold leviO leviM leviDens leviRh at hm
  simp only [Complex.re_ofReal_mul] at *
  have : (m - bb) * (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re ≥ 0 :=
    mul_nonneg (by linarith) hrh
  nlinarith

end UpDivE

end ReciprocityTheory.ChartRestriction.G.AR.Up
