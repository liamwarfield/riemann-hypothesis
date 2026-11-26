module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

open Topology Filter
open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem grad_le_of_minorant (rh Ψ : V n → ℝ) (v0 : V n) (C : ℝ) (hC : 0 < C)
    (hΨ0 : 0 < Ψ v0) (hrh : ContDiffAt ℝ 2 rh v0) (hΨ : ContDiffAt ℝ 2 Ψ v0) (ξ : Fin n → ℂ)
    (hL : (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re ≤ 0)
    (hle : ∀ᶠ v in 𝓝 v0, -C * Real.log (Ψ v) ≤ rh v) (heq : rh v0 = -C * Real.log (Ψ v0)) :
    Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) ≤
      C * (leviV n (fun y => (rh y : ℂ)) v0 ξ).re := by
  set k : ℝ → ℝ := fun t => -C * Real.log t with hkdef
  set ψ : V n → ℝ := fun y => k (Ψ y) with hψdef
  have hk : ContDiffAt ℝ 2 k (Ψ v0) := contDiffAt_const.mul (Real.contDiffAt_log.2 hΨ0.ne')
  have hψ : ContDiffAt ℝ 2 ψ v0 := hk.comp v0 hΨ
  have hrd : DifferentiableAt ℝ rh v0 := hrh.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ v0 := hψ.differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ v0 := hΨ.differentiableAt (by simp)
  have hkd : DifferentiableAt ℝ k (Ψ v0) := hk.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => rh y - ψ y) v0 := by
    filter_upwards [hle] with v hv
    simp only [hψdef, hkdef]
    linarith
  have hfd : fderiv ℝ rh v0 = fderiv ℝ ψ v0 := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (rh y : ℂ)) v0 = wd n j (fun y => (ψ y : ℂ)) v0 := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hdk : deriv k = fun t => -C * t⁻¹ := by
    funext t
    simp only [hkdef]
    rw [deriv_const_mul_field', Real.deriv_log']
  have hddk : deriv (deriv k) = fun t => C * (t ^ 2)⁻¹ := by
    rw [hdk]
    funext t
    rw [deriv_const_mul_field']
    show -C * deriv (fun x : ℝ => x⁻¹) t = _
    rw [deriv_inv]
    ring
  have hwdψ : ∀ j, wd n j (fun y => (ψ y : ℂ)) v0 =
      (((-C * (Ψ v0)⁻¹ : ℝ)) : ℂ) * wd n j (fun y => (Ψ y : ℂ)) v0 := by
    intro j
    rw [show (fun y => (ψ y : ℂ)) = fun y => (k (Ψ y) : ℂ) from rfl, wd_ofReal_comp hkd hΨd, hdk]
  have hchain := leviChain n k Ψ v0 ξ hΨ hk
  rw [hddk, hdk] at hchain

  have hmax : IsLocalMax (fun y => ψ y + (-1) * rh y) v0 := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * rh y) v0 := hψ.add (contDiffAt_const.mul hrh)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hrh) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hrh ξ] at h2
  have hψL : leviV n (fun y => (ψ y : ℂ)) v0 ξ = leviV n (fun y => (k (Ψ y) : ℂ)) v0 ξ := rfl
  rw [hψL, hchain] at h2
  set N := Complex.normSq (∑ j, wd n j (fun y => (Ψ y : ℂ)) v0 * ξ j) with hN
  set LΨ := (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re
  set Lr := (leviV n (fun y => (rh y : ℂ)) v0 ξ).re
  have h3 : (-C * (Ψ v0)⁻¹) * LΨ + C * ((Ψ v0) ^ 2)⁻¹ * N ≤ Lr := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.neg_re, Complex.one_re, neg_mul, one_mul] at h2
    linarith
  have hlhs : Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) =
      (C * (Ψ v0)⁻¹) ^ 2 * N := by
    simp only [hwd, hwdψ, mul_assoc, ← Finset.mul_sum, Complex.normSq_mul, Complex.normSq_ofReal, hN]
    ring
  rw [hlhs]
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hi : 0 < (Ψ v0)⁻¹ := inv_pos.2 hΨ0
  have h4 : 0 ≤ (-C * (Ψ v0)⁻¹) * LΨ := by
    have : -C * (Ψ v0)⁻¹ ≤ 0 := by nlinarith
    nlinarith
  have h5 : (C * (Ψ v0)⁻¹) ^ 2 * N = C * (C * ((Ψ v0) ^ 2)⁻¹ * N) := by
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left (by linarith) hC.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgB

open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open scoped MatrixOrder in
theorem exists_factor {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosSemidef) :
    ∃ y : Matrix (Fin m) (Fin m) ℂ, M = yᴴ * y := by
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  exact ⟨y, hy⟩

theorem amgm_psd {m : ℕ} (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosSemidef) :
    P.det.re ^ ((m : ℝ)⁻¹) ≤ P.trace.re / m := by
  have hH := hP.1
  have hd : P.det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  have ht : P.trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp [← Complex.ofReal_sum]
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.eigenvalues_nonneg i
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin m))
    (fun _ => (m : ℝ)⁻¹) (fun i => hH.eigenvalues i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp) (fun i _ => hnn i)
  rw [hd, ht, ← Real.finsetProd_rpow _ _ (fun i _ => hnn i)]
  calc ∏ i, hH.eigenvalues i ^ ((m : ℝ)⁻¹) ≤ ∑ i, (m : ℝ)⁻¹ * hH.eigenvalues i := h
    _ = (∑ i, hH.eigenvalues i) / m := by rw [← Finset.mul_sum]; field_simp

theorem amgm {m : ℕ} (hm : 0 < m) {A A0 : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef)
    (hA0 : A0.PosDef) :
    A.det.re ^ ((m : ℝ)⁻¹) ≤ A0.det.re ^ ((m : ℝ)⁻¹) * ((A * A0⁻¹).trace.re / m) := by
  have hM : (A0⁻¹).PosDef := hA0.inv
  obtain ⟨y, hy⟩ := exists_factor hM.posSemidef
  have hP : (y * A * yᴴ).PosSemidef := hA.posSemidef.mul_mul_conjTranspose_same y
  have htr : (y * A * yᴴ).trace = (A * A0⁻¹).trace := by
    rw [hy, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  obtain ⟨ha, hai⟩ := det_re_pos_im hA
  obtain ⟨hb, hbi⟩ := det_re_pos_im hA0
  have hdet : (y * A * yᴴ).det.re = A.det.re * (A0.det.re)⁻¹ := by
    have e1 : (y * A * yᴴ).det = A.det * (A0⁻¹).det := by
      rw [hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]; ring
    rw [e1, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_eq_ofReal hA, det_eq_ofReal hA0]
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := amgm_psd hm hP
  rw [hdet, htr, Real.mul_rpow ha.le (inv_nonneg.2 hb.le), Real.inv_rpow hb.le] at h
  have hc : 0 < A0.det.re ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  calc A.det.re ^ ((m : ℝ)⁻¹) = A0.det.re ^ ((m : ℝ)⁻¹) *
        (A.det.re ^ ((m : ℝ)⁻¹) * (A0.det.re ^ ((m : ℝ)⁻¹))⁻¹) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {n : ℕ}

theorem leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => (c : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => (c : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem quad_contDiff {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) :
    ContDiff ℝ ∞ (fun y => τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y)) := by
  refine contDiff_const.sub (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_)
  simp only [Complex.normSq_eq_norm_sq]
  exact (contDiff_norm_sq ℝ).comp ((hℓ a b).restrict_scalars ℝ)

theorem levi_quad_nonpos {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) (x : V n) (ξ : Fin n → ℂ) :
    (leviV n (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) x ξ).re ≤ 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun y => Complex.normSq (ℓ a b y)) x := by
    intro a b
    have h := quad_contDiff (r := 1) (s := 1) 0 (fun _ _ => ℓ a b) (fun _ _ => hℓ a b)
    have h2 : ContDiff ℝ ∞ (fun y => Complex.normSq (ℓ a b y)) := by
      have := h.neg
      simpa using this
    exact h2.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => ∑ b, Complex.normSq (ℓ a b y)) x := fun a =>
    ContDiffAt.sum fun b _ => hc a b
  have hS : ContDiffAt ℝ 2 (fun y => ∑ a, ∑ b, Complex.normSq (ℓ a b y)) x :=
    ContDiffAt.sum fun a _ => hca a
  have e1 : (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) =
      fun y => ((τ + (-1) * ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add contDiffAt_const (contDiffAt_const.mul hS) ξ,
    leviV_const, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hS ξ,
    ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hca ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum (fun b => hc _ b) ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp ((hℓ _ _).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ξ]
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.im_sum, zero_mul, sub_zero]
  have : 0 ≤ ∑ a : Fin r, ∑ b : Fin s, Complex.normSq (∑ j, wd n j (ℓ a b) x * ξ j) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  nlinarith

theorem trace_mul_conjTranspose_re {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℂ) :
    (B * Bᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (B a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem Q_formula {r s : ℕ} (Z : Matrix (Fin r) (Fin s) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((1 - Z * Zᴴ) * (yᴴ * y)).trace.re =
      (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq ((y * Z) a b) := by
  rw [← trace_mul_conjTranspose_re, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re]
  congr 2
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem posDef_swap {r s : ℕ} {Z : Matrix (Fin r) (Fin s) ℂ} (h : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  have hu : IsUnit (1 - Z * Zᴴ).det := isUnit_iff_ne_zero.2 h.det_pos.ne'
  set S := (1 - Z * Zᴴ)⁻¹ with hS
  have hAS : (1 - Z * Zᴴ) * S = 1 := Matrix.mul_nonsing_inv _ hu
  have key : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 := by
    have e : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 + Zᴴ * ((1 - Z * Zᴴ) * S - 1) * Z := by
      simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hAS, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hinv : (1 - Zᴴ * Z)⁻¹ = 1 + Zᴴ * S * Z := Matrix.inv_eq_right_inv key
  have hP : (1 + Zᴴ * S * Z).PosDef :=
    PosDef.one.add_posSemidef ((h.inv).posSemidef.conjTranspose_mul_mul_same Z)
  rw [← hinv] at hP
  exact Matrix.posDef_inv_iff.1 hP

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem block (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq] at hm ⊢
    have hA0 := hv0 k
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - Zof v k * (Zof v k)ᴴ) * (1 - Zof v0 k * (Zof v0 k)ᴴ)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞ (fun v : V (nD f p q) => (y * Zof v k) a b) := by
      intro a b
      simp only [Matrix.mul_apply, Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re -
        ∑ a, ∑ b, Complex.normSq ((fun a b (v : V (nD f p q)) => (y * Zof v k) a b) a b v) := by
      funext v; simp only [hQdef]; rw [hy, Q_formula]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      exact RgB.amgm hm (hv k) hA0
  · rw [min_eq_right hqp] at hm ⊢
    have hA0 := posDef_swap (hv0 k)
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - (Zof v k)ᴴ * Zof v k) * (1 - (Zof v0 k)ᴴ * Zof v0 k)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞
        (fun v : V (nD f p q) => ∑ c, star (y a c) * Zof v k b c) := by
      intro a b
      simp only [Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq
        ((fun a b (v : V (nD f p q)) => ∑ c, star (y a c) * Zof v k b c) a b v) := by
      funext v
      simp only [hQdef]
      have h1 := Q_formula (Zof v k)ᴴ y
      rw [Matrix.conjTranspose_conjTranspose] at h1
      rw [hy, h1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← Complex.normSq_conj]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, conjTranspose_apply, map_sum, Complex.star_def, mul_comm]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      have h := RgB.amgm hm (posDef_swap (hv k)) hA0
      simp only [dk]
      rw [Matrix.det_one_sub_mul_comm, Matrix.det_one_sub_mul_comm (Zof v0 k)]
      exact h

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
