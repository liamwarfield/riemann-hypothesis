module

public import Formalism.PeriodIntegrals.UnimodGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogWindowLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFE
noncomputable section

namespace PI.EF

open Complex DirichletCharacter
open scoped ZMod

variable {N : ℕ} [NeZero N]

theorem zmodL_const_mul (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem norm_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ N := by
  rw [gaussSum]
  calc ‖∑ a, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = N := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

private theorem re_pi_mul_I_mul_div_two (w : ℂ) :
    ((Real.pi : ℂ) * I * w / 2).re = -(Real.pi / 2 * w.im) := by
  rw [show ((Real.pi : ℂ) * I * w / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

private theorem re_neg_pi_mul_I_mul_div_two (w : ℂ) :
    (-(Real.pi : ℂ) * I * w / 2).re = Real.pi / 2 * w.im := by
  rw [show (-(Real.pi : ℂ) * I * w / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

private theorem norm_LFunction_const_mul_le_of_norm_le (χ : DirichletCharacter ℂ N) {c : ℂ} (hc : ‖c‖ ≤ N)
    (w : ℂ) :
    ‖ZMod.LFunction (fun k => c * (χ : ZMod N → ℂ) k) w‖
      ≤ N * ‖ZMod.LFunction (χ : ZMod N → ℂ) w‖ := by
  rw [zmodL_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem norm_L_one_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖LFunction χ⁻¹ w‖ := by
  change ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - w)‖
    ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖
  set L := ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖ with hL
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hs : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ w ≠ 1 := h
  rw [ZMod.LFunction_one_sub _ hs hs']
  set g := gaussSum χ (ZMod.stdAddChar (N := N)) with hg
  have hgN : ‖g‖ ≤ N := norm_gaussSum_le χ
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
    ring
  have hneg : (fun x => (χ : ZMod N → ℂ) (-x)) = χ (-1) • (χ : ZMod N → ℂ) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, neg_one_mul]
  have hc1 : ‖g * χ⁻¹ (-1)‖ ≤ N := by
    rw [norm_mul]
    calc ‖g‖ * ‖χ⁻¹ (-1)‖ ≤ N * 1 :=
          mul_le_mul hgN (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by positivity)
      _ = N := mul_one _
  have hc2 : ‖χ (-1) * (g * χ⁻¹ (-1))‖ ≤ N := by
    rw [norm_mul]
    calc ‖χ (-1)‖ * ‖g * χ⁻¹ (-1)‖ ≤ 1 * N :=
          mul_le_mul (DirichletCharacter.norm_le_one _ _) hc1 (norm_nonneg _) (by positivity)
      _ = N := one_mul _
  have hA : ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖ ≤ N * L := by
    rw [hF]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc1 w
  have hB : ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ N * L := by
    rw [hneg, map_smul, hF]
    have e : (χ (-1) • fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k)
        = fun k => (χ (-1) * (g * χ⁻¹ (-1))) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc2 w
  set E := Real.exp (Real.pi / 2 * |w.im|) with hE
  have he1 : ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le w.im
    have := Real.pi_pos
    nlinarith
  have he2 : ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_neg_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := le_abs_self w.im
    have := Real.pi_pos
    nlinarith
  have hP : ‖(N : ℂ) ^ (w - 1)‖ ≤ (N : ℝ) ^ 4 := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.sub_re, Complex.one_re]
    calc (N : ℝ) ^ (w.re - 1) ≤ (N : ℝ) ^ ((4 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = (N : ℝ) ^ 4 := Real.rpow_natCast _ _
  have hQ : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hGE : ‖Complex.Gamma w‖ * E ≤ 3 * ‖w + 1‖ ^ 5 :=
    Gamma_decay h1 (by linarith)
  have hsum : ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w
      + cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖
      ≤ 2 * E * N * L := by
    calc _ ≤ ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)
              * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := norm_add_le _ _
      _ = ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ * ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖
              * ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ E * (N * L) + E * (N * L) := by gcongr
      _ = 2 * E * N * L := by ring
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(N : ℂ) ^ (w - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖_‖
      ≤ (N : ℝ) ^ 4 * 1 * ‖Complex.Gamma w‖ * (2 * E * N * L) := by gcongr
    _ = 2 * (N : ℝ) ^ 5 * L * (‖Complex.Gamma w‖ * E) := by ring
    _ ≤ 2 * (N : ℝ) ^ 5 * L * (3 * ‖w + 1‖ ^ 5) := by gcongr
    _ = 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * L := by ring

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthDefs
noncomputable section

namespace PI.EF

def ZetaGrowth (C : ℝ) : Prop :=
  ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖(s - 1) * riemannZeta s‖ ≤ C * (|s.im| + 2) ^ 7

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalProofs
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalAbstract
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBoundOfZeroFree
namespace PI.EF.Loc

open Complex Metric Set Filter Topology

theorem logDeriv_bound_of_zero_free (hDL : PI.DiscLog) {g : ℂ → ℂ} {s₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball s₀ R))
    (hz : ∀ z ∈ ball s₀ R, g z ≠ 0) (hb : ∀ z ∈ ball s₀ R, ‖g z‖ ≤ Real.exp M * ‖g s₀‖) :
    ∀ z ∈ closedBall s₀ r, ‖deriv g z / g z‖ ≤ 4 * (r + R) / (R - r) ^ 2 * M := by
  intro z hzr
  obtain ⟨L, hL0, hLd, hLe⟩ := hDL g s₀ R hg hz
  have hR : 0 < R := hr.trans hrR
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hg0 : 0 < ‖g s₀‖ := norm_pos_iff.mpr (hz s₀ hs₀)
  have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun x hx =>
    (hLd x hx).differentiableAt.differentiableWithinAt
  have hre : ∀ x ∈ ball s₀ R, (L x).re ≤ M := by
    intro x hx
    have h1 := hb x hx
    rw [hLe x hx, norm_mul, Complex.norm_exp, mul_comm (Real.exp M)] at h1
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_left h1 hg0)
  have hmem : ∀ u ∈ ball (0 : ℂ) R, s₀ + u ∈ ball s₀ R := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    simpa [dist_eq_norm] using hu
  have hFd : DifferentiableOn ℂ (fun u => L (s₀ + u)) (ball 0 R) := by
    intro u hu
    have h1 : DifferentiableAt ℂ L (s₀ + u) := (hLd _ (hmem u hu)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun v : ℂ => s₀ + v) u := differentiableAt_id.const_add s₀
    exact (h1.comp u h2).differentiableWithinAt
  have hFre : MapsTo (fun u => L (s₀ + u)) (ball 0 R) {w | w.re ≤ M} :=
    fun u hu => hre _ (hmem u hu)
  have hF0 : (fun u => L (s₀ + u)) 0 = 0 := by simp [hL0]
  have hρR : (r + R) / 2 < R := by linarith
  have hbound : ∀ x ∈ closedBall s₀ ((r + R) / 2),
      ‖L x‖ ≤ 2 * M * ((r + R) / 2) / (R - (r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hu : x - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := Complex.borelCaratheodory_zero hM hFd hFre hR hu hF0
    have e : s₀ + (x - s₀) = x := by ring
    simp only [e] at h1
    refine h1.trans ?_
    have hpos : 0 < R - (r + R) / 2 := by linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    nlinarith [mul_nonneg (mul_nonneg hM.le hR.le) (sub_nonneg.mpr hx)]
  have hδ : 0 < (R - r) / 2 := by linarith
  have hzr' : ‖z - s₀‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hzr; exact hzr
  have hsub : closedBall z ((R - r) / 2) ⊆ closedBall s₀ ((r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have : ‖x - s₀‖ ≤ ‖x - z‖ + ‖z - s₀‖ := by
      have := norm_add_le (x - z) (z - s₀)
      simpa using this
    linarith
  have hsubB : closedBall s₀ ((r + R) / 2) ⊆ ball s₀ R := closedBall_subset_ball hρR
  have hdc : DiffContOnCl ℂ L (ball z ((R - r) / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hδ.ne']
    exact hLdiff.mono (hsub.trans hsubB)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc
    (fun x hx => hbound x (hsub (sphere_subset_closedBall hx)))
  have hzB : z ∈ ball s₀ R := hsubB (hsub (mem_closedBall_self hδ.le))
  rw [(hLd z hzB).deriv] at hc
  refine hc.trans (le_of_eq ?_)
  have e1 : R - (r + R) / 2 = (R - r) / 2 := by ring
  have hne : R - r ≠ 0 := by linarith
  rw [e1]
  field_simp
  ring

end PI.EF.Loc
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.NormLogDerivReflLe
noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology ComplexConjugate

def refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ := ((R : ℂ) ^ 2 - conj (ρ - s₀) * (z - s₀)) / R

lemma norm_refl_sphere {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by
  have hw : ‖z - s₀‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀) := by
    rw [mul_conj, normSq_eq_norm_sq, hw]
    push_cast
    ring
  have hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ) := by
    simp only [map_sub]
    ring
  unfold refl
  rw [hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp

lemma le_norm_refl {s₀ ρ z : ℂ} {R R' : ℝ} (hR : 0 < R) (hρ : ρ ∈ closedBall s₀ R')
    (hz : z ∈ closedBall s₀ R) : R - R' ≤ ‖refl s₀ R ρ z‖ := by
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  have hw : ‖z - s₀‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  unfold refl
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR]
  have h1 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2 : ‖conj (ρ - s₀) * (z - s₀)‖ ≤ R' * R := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg _).trans ha)
  have h3 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj (ρ - s₀) * (z - s₀))
  rw [h1] at h3
  nlinarith

lemma refl_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) : refl s₀ R ρ s₀ = R := by
  have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold refl
  rw [sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]

lemma hasDerivAt_refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) :
    HasDerivAt (refl s₀ R ρ) (-(conj (ρ - s₀) * 1) / R) z :=
  ((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)

lemma differentiable_refl (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) :=
  fun z => (hasDerivAt_refl s₀ R ρ z).differentiableAt

lemma norm_logDeriv_refl_le {s₀ ρ z : ℂ} {R R' : ℝ} (hR'R : R' < R) (hR : 0 < R)
    (hρ : ρ ∈ closedBall s₀ R') (hz : z ∈ closedBall s₀ R) :
    ‖logDeriv (refl s₀ R ρ) z‖ ≤ R' / (R * (R - R')) := by
  have hpos : 0 < R - R' := sub_pos.mpr hR'R
  have hl := le_norm_refl hR hρ hz
  have hn : 0 < ‖refl s₀ R ρ z‖ := lt_of_lt_of_le hpos hl
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  rw [logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one,
    Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div,
    div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]
  have h4 := mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)
  nlinarith

lemma logDeriv_prod_pow_mul {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by
  have hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s :=
    by
      have h5 := DifferentiableAt.finsetProd (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
      rwa [Finset.prod_fn] at h5
  rw [logDeriv_fun_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]
  congr 1
  have h6 := logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s)
    (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
  rw [Finset.prod_fn] at h6
  rw [h6]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact logDeriv_fun_pow (hφd ρ hρ) (m ρ)

lemma order_eq_of_factor {f h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ Z) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) (hf : AnalyticAt ℂ f ρ) (hh : DifferentiableOn ℂ h U) (hhρ : h ρ ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) :
    analyticOrderNatAt f ρ = m ρ := by
  have hha : AnalyticAt ℂ h ρ := hh.analyticAt hU
  have hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    by
      have h7 := Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ)
        (fun ρ' _ => by fun_prop)
      rw [Finset.prod_fn] at h7
      exact h7.mul hha
  have hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨_, hg, hg0, ?_⟩
    filter_upwards [hU] with z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]
  simp [analyticOrderNatAt, hord]

end PI.EF.Loc
end
end

noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology

def locC (r R' R : ℝ) : ℝ :=
  4 * (r + R') / (R' - r) ^ 2 + R' / (R * (R - R')) / Real.log (R / R')

lemma locC_pos {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  have h1 : 0 < 4 * (r + R') / (R' - r) ^ 2 :=
    div_pos (by linarith) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have h2 : 0 < R' / (R * (R - R')) / Real.log (R / R') :=
    div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog
  unfold locC
  linarith

section core

variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}

def gfun (s₀ : ℂ) (R : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∏ ρ ∈ Z, (refl s₀ R ρ z) ^ (m ρ)) * h z

private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn

lemma gfun_bounds (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N := ⟨_, rfl⟩
  have hs₀R' : s₀ ∈ closedBall s₀ R' := mem_closedBall_self hR'.le
  have hs₀R : s₀ ∈ closedBall s₀ R := mem_closedBall_self hR.le
  have hhs₀ : h s₀ ≠ 0 := hh0 s₀ hs₀R'
  have hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀ := by
    have hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ := fun ρ _ => by
      rw [refl_center hR]
    simp only [gfun]
    rw [Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]
  have hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖ := by
    rw [hg₀, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖ := by
    rw [hfac s₀ hs₀R, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ∏ ρ ∈ Z, ‖(s₀ - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖s₀ - ρ‖ ^ m ρ := by simp only [norm_pow]
      _ ≤ ∏ ρ ∈ Z, R' ^ m ρ := by
        refine Finset.prod_le_prod₀ (fun ρ _ => by positivity) fun ρ hρ => ?_
        have hρ' : ρ ∈ closedBall s₀ R' := ((hZ ρ).1 hρ).1
        rw [mem_closedBall, dist_eq_norm] at hρ'
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) hρ' _
      _ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]
  have hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖ := by
    intro z hz
    rw [hfac z (sphere_subset_closedBall hz)]
    simp only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]
  have hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hR.ne']
    exact differentiableOn_gfun_of_differentiableOn hh
  have hmax : ∀ z ∈ closedBall s₀ R,
      ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖) := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball s₀ hR.ne'])
    intro w hw
    rw [frontier_ball s₀ hR.ne'] at hw
    rw [hsphere w hw]
    exact (hb w (sphere_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)
  have hkey : R ^ N ≤ Real.exp M * R' ^ N := by
    have h1 := hmax s₀ hs₀R
    rw [hg₀n, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hg₀n]
    refine (hmax z hz).trans ?_
    have hp : R' ^ N ≤ R ^ N := pow_le_pow_left₀ hR'.le hR'R.le N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      (Real.exp_pos M).le
  · rw [hN]
    have hl := Real.log_le_log (pow_pos hR N) hkey
    rw [Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow,
      Real.log_pow] at hl
    rw [Real.log_div hR.ne' hR'.ne', mul_sub]
    linarith

theorem core (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  intro s hs hfs
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨hg, hN⟩ := gfun_bounds hR' hR'R hZ hh hh0 hfac hb
  have hsR' : s ∈ closedBall s₀ R' := closedBall_subset_closedBall hrR'.le hs
  have hsball : s ∈ ball s₀ R := closedBall_subset_ball (hrR'.trans hR'R) hs
  have hsR : s ∈ closedBall s₀ R := ball_subset_closedBall hsball
  have hnhds : closedBall s₀ R ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall
  have hhs : h s ≠ 0 := hh0 s hsR'
  have hhd : DifferentiableAt ℂ h s := hh.differentiableAt hnhds
  have hρs : ∀ ρ ∈ Z, s - ρ ≠ 0 := by
    intro ρ hρ h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    exact hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)
  have hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem hnhds fun z hz => hfac z hz
  have hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s := by
    have e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s := by
      rw [logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    rw [e1]
    refine (logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs
      (fun ρ _ => by fun_prop) hhs hhd).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0 := by
    intro z hz ρ hρ h0
    have h1 := le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz
    rw [h0, norm_zero] at h1
    linarith
  have hlg : logDeriv (gfun s₀ R Z m h) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s :=
    logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ)
      (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd
  have hsub : ball s₀ R' ⊆ closedBall s₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)
  have hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0 := by
    intro z hz
    simp only [gfun]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ))
      (hh0 z (ball_subset_closedBall hz))
  have hLg := logDeriv_bound_of_zero_free hDL hr hrR' hM
    (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs
  have hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M := by
    rw [logDeriv_apply]
    exact hLg
  have hK : 0 ≤ R' / (R * (R - R')) := div_nonneg hR'.le (mul_pos hR (by linarith)).le
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R') := by
    exact (le_div_iff₀ hlog).mpr hN
  have hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤
      R' / (R * (R - R')) / Real.log (R / R') * M := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (R' / (R * (R - R'))) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul]
          have hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ) := by
            exact Complex.norm_natCast _
          rw [hn]
          exact mul_le_mul_of_nonneg_left
            (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)
      _ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) :=
          mul_le_mul_of_nonneg_right hNle hK
      _ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring
  have hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) =
      logDeriv (gfun s₀ R Z m h) s -
        ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s := by
    rw [hlf, hlg]
    ring
  rw [hdiff]
  calc _ ≤ ‖logDeriv (gfun s₀ R Z m h) s‖ +
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sub_le _ _
    _ ≤ 4 * (r + R') / (R' - r) ^ 2 * M + R' / (R * (R - R')) / Real.log (R / R') * M :=
        add_le_add hLg' hsumB
    _ = locC r R' R * M := by
        unfold locC
        ring

end core

theorem local_abstract (hDF : PI.DiscFactor) (hDL : PI.DiscLog) {r R' R : ℝ} (hr : 0 < r)
    (hrR' : r < R') (hR'R : R' < R) (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall s₀ R)) (hf0 : f s₀ ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ({ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  have hR' : 0 < R' := hr.trans hrR'
  have hfd : DifferentiableOn ℂ f (closedBall s₀ R) := hf.differentiableOn
  obtain ⟨Z, m, h, hZ, -, hh, hh0, hfac⟩ := hDF f s₀ R R' hR' hR'R hfd hf0
  have hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hZ ρ).symm
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := by
    intro ρ hρ
    have hρR : ρ ∈ ball s₀ R := closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1
    exact order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR)
      (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall)
      (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)
  refine ⟨by rw [hset]; exact Z.finite_toSet, ?_⟩
  intro s hs hfs
  have hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) :=
    Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
  rw [hset, finsum_mem_coe_finset, hsum]
  have hC : 0 < locC r R' R := locC_pos hr hrR' hR'R
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεC : 0 < ε / locC r R' R := div_pos hε hC
  have hM' : 0 < M + ε / locC r R' R := add_pos_of_nonneg_of_pos hM hεC
  have hb' : ∀ z ∈ closedBall s₀ R,
      ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖ := fun z hz =>
    (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  have key := core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs
  have hCε : locC r R' R * (ε / locC r R' R) = ε := by
    exact mul_div_cancel₀ ε hC.ne'
  calc _ ≤ locC r R' R * (M + ε / locC r R' R) := key
    _ = locC r R' R * M + ε := by rw [mul_add, hCε]

end PI.EF.Loc
end
end

namespace PI.EF

theorem localAbstract_of (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩

end PI.EF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthZeta
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have h0 := norm_L_one_sub_le (N := 1) hp h1 h2 (Or.inr h)
  simpa [DirichletCharacter.LFunction_modOne_eq] using h0

theorem zeta_right (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := by
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hre : 0 < s.re := by linarith
  have hb := hZ s hre hs
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have ht := abs_nonneg s.im
  have hs_le : ‖s‖ ≤ 8 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hs1_le : ‖s - 1‖ ≤ 7 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hre]; linarith
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖s - 1‖ + 1 + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
        rw [mul_add, mul_add, mul_one_div_cancel hn1.ne']
        ring
    _ ≤ (7 + |s.im|) + 1 + (7 + |s.im|) * (8 + |s.im|) * (1 + 2) := by gcongr
    _ ≤ 51 * (|s.im| + 2) ^ 2 := by nlinarith

theorem zeta_left (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re < 1 / 2)
    (h3 : 1 / 2 ≤ ‖s‖) : ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h3
    norm_num at h3
  have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw : (1 - s) ≠ 1 := by
    intro h0
    apply hs0
    linear_combination -h0
  have hz1 := zeta_one_sub_le hw1 hw2 hw
  rw [sub_sub_cancel] at hz1
  have hwre : 0 < (1 - s).re := by linarith
  have hz2 := hZ (1 - s) hwre hw
  have ht := abs_nonneg s.im
  have hwim : |(1 - s).im| = |s.im| := by simp
  have hn : ‖1 - s - 1‖ = ‖s‖ := by rw [show 1 - s - 1 = -s by ring, norm_neg]
  have hinv1 : 1 / ‖1 - s - 1‖ ≤ 2 := by
    rw [hn, div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / (1 - s).re ≤ 2 := by rw [div_le_iff₀ hwre]; linarith
  have hw_le : ‖1 - s‖ ≤ 5 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hwim, abs_of_pos hwre]
    linarith
  have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e : |(1 - s + 1).im| = |s.im| := by simp
    have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
    rw [e, e2, abs_of_pos (by linarith)]
    linarith
  have hzw : ‖riemannZeta (1 - s)‖ ≤ 18 + 3 * |s.im| := by
    calc ‖riemannZeta (1 - s)‖ ≤ 1 + 1 / ‖1 - s - 1‖ + ‖1 - s‖ * (1 + 1 / (1 - s).re) := hz2
      _ ≤ 1 + 2 + (5 + |s.im|) * (1 + 2) := by gcongr
      _ = 18 + 3 * |s.im| := by ring
  have hsn : ‖s - 1‖ = ‖1 - s‖ := norm_sub_rev _ _
  rw [norm_mul, hsn]
  calc ‖1 - s‖ * ‖riemannZeta s‖ ≤ ‖1 - s‖ * (6 * ‖1 - s + 1‖ ^ 5 * ‖riemannZeta (1 - s)‖) := by gcongr
    _ ≤ (5 + |s.im|) * (6 * (6 + |s.im|) ^ 5 * (18 + 3 * |s.im|)) := by gcongr
    _ ≤ (3 * (|s.im| + 2)) * (6 * (3 * (|s.im| + 2)) ^ 5 * (9 * (|s.im| + 2))) := by
        gcongr <;> linarith
    _ = 39366 * (|s.im| + 2) ^ 7 := by ring
    _ ≤ 48114 * (|s.im| + 2) ^ 7 := by gcongr; norm_num

theorem zetaGrowth_of (hZ : PI.ZetaBoundRight) : ZetaGrowth 300000 := by
  intro s hs1 hs2
  have ht := abs_nonneg s.im
  have h2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hp7 : (|s.im| + 2) ^ 2 ≤ (|s.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := zeta_right hZ hr hs2
      _ ≤ 300000 * (|s.im| + 2) ^ 7 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ |s.im| + 2) 2]
  · push_neg at hr
    by_cases hn : 1 / 2 ≤ ‖s‖
    · calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := zeta_left hZ hs1 hr hn
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr; norm_num
    · push_neg at hn
      have hK : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 2)),
          ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by
        intro z hz
        rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hz
        have hre : |z.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z).trans hz.le
        have him : |z.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z).trans hz.le
        have hzi := abs_nonneg z.im
        rcases lt_or_ge z.re (1 / 2) with hlt | hge
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (|z.im| + 2) ^ 7 :=
                zeta_left hZ (by linarith [(abs_le.1 hre).1]) hlt (by rw [hz])
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by gcongr; linarith
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 51 * (|z.im| + 2) ^ 2 :=
                zeta_right hZ hge (by linarith [(abs_le.1 hre).2])
            _ ≤ 51 * (5 / 2 : ℝ) ^ 2 := by gcongr; linarith
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by norm_num
      have hd : DiffContOnCl ℂ (fun z => (z - 1) * riemannZeta z) (Metric.ball (0 : ℂ) (1 / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        intro z hz
        have hz1 : z ≠ 1 := by
          intro h
          rw [h, Metric.mem_closedBall, dist_zero_right, norm_one] at hz
          norm_num at hz
        exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt
      have hmem : s ∈ closure (Metric.ball (0 : ℂ) (1 / 2)) := subset_closure (mem_ball_zero_iff.2 hn)
      have hb := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hK hmem
      calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := hb
        _ ≤ 300000 * 2 ^ 7 := by norm_num
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthMain
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

theorem L_right (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 8) :
    ‖LFunction χ w‖ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by
  have hre : 0 < w.re := by linarith
  have hb := hB N χ hχ1 w hre
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg w.im
  have hw : ‖w‖ ≤ 8 + |w.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|) := by
    rw [div_le_iff₀ hre]
    nlinarith [norm_nonneg w]
  calc ‖LFunction χ w‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + ‖w‖ / w.re) := hb
    _ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 2 * (8 + |w.im|)) := by gcongr
    _ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by nlinarith

theorem L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg s.im
  have hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := one_le_mul_of_one_le_of_one_le hN (by linarith)
  by_cases hr : 1 / 2 ≤ s.re
  · calc ‖LFunction χ s‖ ≤ 37 * ((N : ℝ) * (|s.im| + 2)) := L_right hB hχ1 hr h2
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
        have : (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7 := le_self_pow₀ hX (by norm_num)
        nlinarith
  · push_neg at hr
    have h0 : χ 0 = 0 := by
      by_cases hN1 : N = 1
      · subst hN1
        exfalso
        apply hχ1
        exact MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp
      · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
        exact χ.map_nonunit not_isUnit_zero
    have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hL1 := norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)
    rw [sub_sub_cancel] at hL1
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
    have hL2 := L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hwim : |(1 - s).im| = |s.im| := by simp
    rw [hwim] at hL2
    have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e : |(1 - s + 1).im| = |s.im| := by simp
      have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
      rw [e, e2, abs_of_pos (by linarith)]
      linarith
    calc ‖LFunction χ s‖ ≤ 6 * (N : ℝ) ^ 5 * ‖1 - s + 1‖ ^ 5 * ‖LFunction χ⁻¹ (1 - s)‖ := hL1
      _ ≤ 6 * (N : ℝ) ^ 5 * (6 + |s.im|) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 5 * (3 * (|s.im| + 2)) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by
          gcongr
          linarith
      _ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)

theorem lGrowth_of (hB : PI.LBoundRight) {C : ℝ} (hZ : ZetaGrowth C) :
    LGrowth 7 (max C 53946) := by
  intro N _ χ hχ s h1 h2
  have e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ) := fun x => by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e7]
  by_cases hc : χ = 1
  · subst hc
    have hN : N = 1 := by
      have h0 := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h0
      exact h0.symm
    subst hN
    simp only [del1, ↓reduceIte, one_mul]
    rw [show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]
    refine le_trans (hZ s h1 h2) ?_
    simp only [Nat.cast_one, one_mul]
    gcongr
    exact le_max_left _ _
  · simp only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]
    calc ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := L_nontriv_growth hB hχ hc h1 h2
      _ ≤ max C 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
          gcongr
          exact le_max_right _ _

end PI.EF
end
end

noncomputable section

namespace PI.EF

theorem localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C :=
  localLemma_of hLI (localAbstract_of hDF hDL)
    ⟨7, max 300000 53946, by norm_num, lt_max_of_lt_left (by norm_num),
      lGrowth_of hLB (zetaGrowth_of hZB)⟩ zeroLocus hZW

theorem explicitFormula_main (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) : PI.ExplicitFormula :=
  explicitFormula_of_local hZW (localLemma_of_helpers hZW hDF hDL hLB hZB hLI) perron_gluing_sides

end PI.EF
end
end

theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
