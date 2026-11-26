module

public import Formalism.LandauZeroFreeBounds.NoZeroComplex
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszOf

@[expose] public section

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem lfunction_one_upper_bound : LFunctionOneUpperBound := by
  refine ⟨38 * Real.exp (3 / 2), ?_⟩
  intro q _ χ hχ
  have hq : 3 ≤ q := three_le_modulus_of_ne_one χ hχ
  have hlog : 2 ≤ Real.log (3 * (q : ℝ)) := two_le_log_three_mul q hq
  have hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ))) := div_pos (by norm_num) (by linarith)
  exact lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith)
    (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire
open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

theorem zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact Function.update_of_ne hz _ _
    have hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · unfold zetaSubPole
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

theorem zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _

theorem dirichlet_product_entire : BqEntire := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    exact ((DirichletCharacter.differentiable_LFunction h₁).mul
      (DirichletCharacter.differentiable_LFunction h₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ)
  have hds : Differentiable ℂ (dslope P 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hPd.differentiableOn
  refine ⟨fun s => zetaSubPole s * P s + dslope P 1 s,
    (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  show _ = zetaSubPole s * P s + dslope P 1 s + _
  rw [dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]
  simp only [Fbq, lamBq, hP]
  field_simp
  ring

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExcBoundOf
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma log_le_const_mul_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log (3 * x) ≤ K * x ^ δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h4 : Real.log 3 ≤ Real.log 3 * x ^ δ := by nlinarith
  have h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ := by ring
  rw [Real.log_mul (by norm_num) hx0.ne', h5]
  linarith

lemma rpow_neg_eq_inv_pow (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]

theorem exceptional_zero_bound_of : ExcBoundOf := by
  unfold ExcBoundOf ExcBound
  intro hS hL ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨c0, hc0, hS'⟩ := hS (ε / 3) hε3
  obtain ⟨C, hC⟩ := hL
  obtain ⟨K, hK, hKb⟩ := log_le_const_mul_rpow (ε / 3) hε3
  obtain ⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M := ⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  have hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2)) :=
    lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))
  refine ⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩
  intro q _ χ β hχ2 hχ1 hβ
  have hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K := min_le_left _ _
  have hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2) := min_le_right _ _
  generalize min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hu1 : 1 ≤ (q : ℝ) ^ (ε / 3) := Real.one_le_rpow hq1 hε3.le
  have hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹ := by
    have h := rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)
    simpa using h
  have hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹ := Real.rpow_neg hq0.le _
  have hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3) := hKb q hq1
  have hlog_pos : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hβ1 : β < 1 := by
    by_contra hge
    simp only [not_lt] at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ
  have hlow := hS' q χ hχ2 hχ1
  rw [hq3] at hlow
  rw [hqε]
  generalize (q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢
  have hu0 : 0 < u := by linarith
  by_cases hcase : β ≤ 1 - 1 / Real.log (3 * q)
  · have key : c * Real.log (3 * q) ≤ u ^ 3 := by
      have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
      calc c * Real.log (3 * q) ≤ (1 / K) * (K * u) :=
            mul_le_mul hcK hlogK hlog_pos.le (div_pos one_pos hK).le
        _ = u := by field_simp
        _ ≤ u ^ 3 := hu3
    have h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]
      exact key
    linarith
  · simp only [not_le] at hcase
    have hdiff := DirichletCharacter.differentiable_LFunction hχ1
    have hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 -
        (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤
        (C * Real.log (3 * q) ^ 2) * (1 - β) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1)
        (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩
      · intro t _
        exact ((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      · intro t ht
        exact hC q χ hχ1 t (by linarith [ht.1]) ht.2.le
    simp only [hβ, sub_zero, Complex.ofReal_one] at hmvt
    have h1β : 0 < 1 - β := by linarith
    have hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hlog_pos.le hlogK 2
    have hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2 :=
      mul_le_mul hCM hlog2 (sq_nonneg _) hM.le
    have hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β) :=
      le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))
    have hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β) := by
      have h := mul_le_mul_of_nonneg_right hmain hu0.le
      have e1 : c0 * u⁻¹ * u = c0 := by field_simp
      have e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β) := by ring
      linarith
    have hMKu : 0 < M * K ^ 2 * u ^ 3 := mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)
    have hfin : c * (u ^ 3)⁻¹ ≤ 1 - β := by
      calc c * (u ^ 3)⁻¹ ≤ c0 / (M * K ^ 2) * (u ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right hc2 (inv_nonneg.2 (pow_pos hu0 3).le)
        _ = c0 / (M * K ^ 2 * u ^ 3) := by field_simp
        _ ≤ 1 - β := by
          rw [div_le_iff₀ hMKu]
          linarith
    linarith

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf
section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LeOfSecondDifferenceBound
noncomputable section

namespace Formalism.ZeroFreeDirichlet


set_option maxHeartbeats 800000 in
lemma le_of_second_difference_bound {y c₀ C N eY ey h : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hC : 0 ≤ C)
    (hh : h = Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)))
    (hey0 : 0 ≤ ey) (heY0 : 0 ≤ eY) (hey : ey ≤ h ^ 2) (heY : eY ≤ h ^ 2)
    (hmain : y * h * N ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (C * (y * (1 + h)) * eY) + y * (1 + h) * (C * y * ey)) :
    N ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hc2 : c₀ ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc01
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hlogmul : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) := by
    have hh0' : 0 < h := by rw [hh]; exact Real.exp_pos _
    exact Real.log_mul hy0.ne' (by linarith)
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  set g := Real.exp (-(c₀ / 4) * s) with hgdef
  have hg0 : 0 < g := Real.exp_pos _
  have hg1 : g ≤ 1 := by
    rw [hgdef, Real.exp_le_one_iff]
    have : 0 ≤ c₀ / 4 * s := by positivity
    linarith
  have hhg : h = g * g := by
    rw [hh, hgdef, ← Real.exp_add]; congr 1; ring
  have hh0 : 0 < h := by rw [hhg]; positivity
  have hhle : h ≤ g := by rw [hhg]; exact mul_le_of_le_one_left hg0.le hg1
  have hh1 : h ≤ 1 := le_trans hhle hg1
  have hyg : Real.exp (s ^ 2 / 2) ≤ y * g := by
    have hyL : y = Real.exp L := (Real.exp_log hy0).symm
    rw [hgdef, hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hB : L + 1 ≤ 2 * (y * g) := by
    have : 0 ≤ (s ^ 2 / 2) ^ 2 / 2 := by positivity
    linarith
  have ht := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ c₀ / 4 * s by positivity)
  have hgt : g * Real.exp (c₀ / 4 * s) = 1 := by
    rw [hgdef, ← Real.exp_add, show -(c₀ / 4) * s + c₀ / 4 * s = 0 by ring, Real.exp_zero]
  have hA1 : g * (c₀ / 4 * s) ^ 2 ≤ 2 := by
    have h0 : 0 ≤ c₀ / 4 * s := by positivity
    have : (c₀ / 4 * s) ^ 2 ≤ 2 * Real.exp (c₀ / 4 * s) := by linarith
    calc g * (c₀ / 4 * s) ^ 2 ≤ g * (2 * Real.exp (c₀ / 4 * s)) :=
          mul_le_mul_of_nonneg_left this hg0.le
      _ = 2 * (g * Real.exp (c₀ / 4 * s)) := by ring
      _ = 2 := by rw [hgt]; ring
  have hA : c₀ ^ 2 * g * (L + 1) ≤ 33 := by
    have e : c₀ ^ 2 * g * (L + 1) = 16 * (g * (c₀ / 4 * s) ^ 2) + c₀ ^ 2 * g := by
      rw [← hss]; ring
    have : c₀ ^ 2 * g ≤ 1 := mul_le_one₀ hc2 hg0.le hg1
    rw [e]; linarith
  have hA' : g * (L + 1) ≤ 33 / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : g * (L + 1) * c₀ ^ 2 = c₀ ^ 2 * g * (L + 1) := by ring
    rw [e]; exact hA
  have hlog : Real.log (y * (1 + h)) ≤ L + 1 := by
    rw [hlogmul]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + h)
    linarith
  have hP : 0 < y * h := by positivity
  have hyh1 : y * (1 + h) - y = y * h := by ring
  rw [hyh1] at hmain
  have T1 : (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h) * ((y * h + 1) * (L + 1)) := by
    have : (y * h) * Real.log (y * (1 + h)) ≤ (y * h) * (L + 1) :=
      mul_le_mul_of_nonneg_left hlog hP.le
    calc (y * h + 1) * ((y * h) * Real.log (y * (1 + h))) ≤ (y * h + 1) * ((y * h) * (L + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (y * h) * ((y * h + 1) * (L + 1)) := by ring
  have T1' : (y * h + 1) * (L + 1) ≤ (33 / c₀ ^ 2 + 2) * (y * g) := by
    calc (y * h + 1) * (L + 1) = (y * g) * (g * (L + 1)) + (L + 1) := by rw [hhg]; ring
      _ ≤ (y * g) * (33 / c₀ ^ 2) + 2 * (y * g) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' (by positivity)) hB
      _ = (33 / c₀ ^ 2 + 2) * (y * g) := by ring
  have T2 : 2 * y ^ 2 * h ^ 2 ≤ (y * h) * (2 * (y * g)) := by
    have : y * h ≤ y * g := mul_le_mul_of_nonneg_left hhle hy0.le
    calc 2 * y ^ 2 * h ^ 2 = (y * h) * (2 * (y * h)) := by ring
      _ ≤ (y * h) * (2 * (y * g)) := mul_le_mul_of_nonneg_left (by linarith) hP.le
  have hhh : (1 + h) * h ≤ 2 * g := by
    have h1 : h * h ≤ h := mul_le_of_le_one_left hh0.le hh1
    have e : (1 + h) * h = h + h * h := by ring
    rw [e]; linarith
  have hCy : 0 ≤ C * y := mul_nonneg hC hy0.le
  have T3 : y * (C * (y * (1 + h)) * eY) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ C * (y * (1 + h)) := mul_nonneg hC (by positivity)
    have : C * (y * (1 + h)) * eY ≤ C * (y * (1 + h)) * h ^ 2 := mul_le_mul_of_nonneg_left heY hk
    calc y * (C * (y * (1 + h)) * eY) ≤ y * (C * (y * (1 + h)) * h ^ 2) :=
          mul_le_mul_of_nonneg_left this hy0.le
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T4 : y * (1 + h) * (C * y * ey) ≤ (y * h) * (2 * C * (y * g)) := by
    have hk : 0 ≤ y * (1 + h) * (C * y) := mul_nonneg (by positivity) hCy
    have : y * (1 + h) * (C * y) * ey ≤ y * (1 + h) * (C * y) * h ^ 2 :=
      mul_le_mul_of_nonneg_left hey hk
    calc y * (1 + h) * (C * y * ey) = y * (1 + h) * (C * y) * ey := by ring
      _ ≤ y * (1 + h) * (C * y) * h ^ 2 := this
      _ = (y * h) * (C * y * ((1 + h) * h)) := by ring
      _ ≤ (y * h) * (C * y * (2 * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh hCy) hP.le
      _ = (y * h) * (2 * C * (y * g)) := by ring
  have T1'' := mul_le_mul_of_nonneg_left T1' hP.le
  have hfin : (33 / c₀ ^ 2 + 2) * (y * g) + 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) ≤
      (128 / c₀ ^ 2 + 2 + 4 * C) * y * g := by
    have h95 : 2 ≤ 95 / c₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h95 (by positivity : (0 : ℝ) ≤ y * g)
    have e1 : (128 / c₀ ^ 2 + 2 + 4 * C) * y * g =
        (33 / c₀ ^ 2 + 2) * (y * g) + 95 / c₀ ^ 2 * (y * g) + 2 * C * (y * g) + 2 * C * (y * g) := by
      ring
    rw [e1]; linarith
  have hfin' := mul_le_mul_of_nonneg_left hfin hP.le
  refine le_of_mul_le_mul_left ?_ hP
  linarith

lemma mul_le_of_log_bounds {y c₀ K lq : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hK : K * Real.log 2 ≤ Real.log y) (hK0 : 0 ≤ K) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ c₀ / 4 * Real.sqrt (Real.log y)) :
    K * lq ≤ 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hyL : y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  have hKL : K ≤ 2 * L := by nlinarith
  have hlq' : lq ≤ s / 4 := by
    have : c₀ / 4 * s ≤ 1 / 4 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hKlq : K * lq ≤ (2 * L) * (s / 4) := mul_le_mul hKL hlq' hlq0 (by positivity)
  have hexp : Real.exp (s ^ 2 / 2) ≤ y * Real.exp (-(c₀ / 4) * s) := by
    rw [hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hpoly : (2 * L) * (s / 4) ≤ 16 * (1 + s ^ 2 / 2 + (s ^ 2 / 2) ^ 2 / 2) := by
    rw [← hss]; nlinarith [sq_nonneg (s ^ 2 - s), sq_nonneg s]
  have e : 16 * y * Real.exp (-(c₀ / 4) * s) = 16 * (y * Real.exp (-(c₀ / 4) * s)) := by ring
  rw [e]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SumVonMangoldtNotCoprimeLe
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def weightedPartialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * ((x / n - 1 : ℝ) : ℂ)

def partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n

lemma sum_Icc_eq_add_sum_Ioc (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]

lemma weightedSum_identity (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by
  unfold weightedPartialSumUpTo partialSumUpTo
  rw [sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]
  simp only [mul_add, Finset.mul_sum]
  rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring

lemma norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  have hY1 : 1 ≤ Y := le_trans hy hyY
  have hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊,
      ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : y < (n : ℝ) := by
      have := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    have hn2 : (n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      linarith
    have hnpos : (0:ℝ) < n := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ y * (Y / n - 1) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg, le_div_iff₀ hnpos]; linarith
    have hB : y * (Y / n - 1) ≤ Y - y := by
      have e : y * (Y / n - 1) = (Y - n) * (y / n) := by field_simp
      rw [e]
      have h3 : y / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have h4 : 0 ≤ Y - n := by linarith
      nlinarith
    rw [abs_of_nonneg hA]
    have hf' : ‖f n‖ ≤ Real.log Y :=
      calc ‖f n‖ ≤ Λ n := hf n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log hnpos hn2
    calc ‖f n‖ * (y * (Y / n - 1)) ≤ Real.log Y * (Y - y) :=
          mul_le_mul hf' hB hA (Real.log_nonneg hY1)
      _ = (Y - y) * Real.log Y := by ring
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, (Y - y) * Real.log Y := Finset.sum_le_sum hterm
    _ = ((Ioc ⌊y⌋₊ ⌊Y⌋₊).card : ℝ) * ((Y - y) * Real.log Y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]
      have h1 := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 := Nat.lt_floor_add_one y
      linarith

lemma norm_weightedSum_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  rw [weightedSum_identity f hyY, add_sub_cancel_left]
  exact norm_sum_Ioc_le f hf hy hyY

lemma sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg
  have hgle : ∀ n, g n ≤ Λ n := fun n => by
    simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hN⟩, hgn⟩ := hn
    have hΛ : Λ n ≠ 0 := by intro h; apply hgn; simp [hg, h]
    have hnc : ¬ n.Coprime q := by intro h; apply hgn; simp [hg, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hpq : p ∣ q := by
      by_contra hc
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hN
    rw [Nat.mem_divisors]
    exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩
  calc ∑ n ∈ Icc 1 N, g n = ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), Λ n := Finset.sum_le_sum fun n _ => hgle n
    _ ≤ ∑ n ∈ (q ^ K).divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = (K : ℝ) * Real.log q := by rw [vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

lemma one_apply_natCast {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.AbsZeroTermSecondDifferenceLe
noncomputable section

namespace Formalism.ZeroFreeDirichlet

private theorem one_add_rpow_le_one_add_mul {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 + s) ^ p ≤ 1 + p * s := by
  have t := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1)
    (by linarith : (0:ℝ) ≤ 1 + s) zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at t
  nlinarith [t]

private theorem le_one_add_mul_log_one_add {h : ℝ} (hh : 0 ≤ h) : h ≤ (1 + h) * Real.log (1 + h) := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have t := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at t
  have e : (1 + h) * (1 + h)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  nlinarith [mul_le_mul_of_nonneg_left t h1.le]

lemma abs_zero_term_second_difference_le {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (_hh1 : h ≤ 1) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β < 1) :
    |(y * (1 + h)) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
        + y * h * (y ^ β / β)| ≤ 2 * y ^ 2 * h ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hβ0 : 0 < β := by linarith
  have hq : 0 < 1 - β := by linarith
  have hβne : β ≠ 0 := hβ0.ne'
  have hβ1ne : β - 1 ≠ 0 := by linarith
  have hq1ne : 1 - β ≠ 0 := hq.ne'
  have hmul : (y * (1 + h)) ^ β = y ^ β * (1 + h) ^ β := Real.mul_rpow hy0 h1.le
  have hAq : (1 + h) ^ β * (1 + h) ^ (1 - β) = 1 + h := by
    have e : β + (1 - β) = 1 := by ring
    rw [← Real.rpow_add h1, e, Real.rpow_one]
  have hBern : (1 + h) ^ (1 - β) ≤ 1 + (1 - β) * h :=
    one_add_rpow_le_one_add_mul hh.le hq.le (by linarith)
  have hD0 : (1 + h) ^ β ≤ 1 + β * h := one_add_rpow_le_one_add_mul hh.le hβ0.le hβ2.le
  have hA0 : 0 ≤ (1 + h) ^ β := Real.rpow_nonneg h1.le _
  have hB0 : 0 ≤ y ^ β := Real.rpow_nonneg hy0 _
  have hBy : y ^ β ≤ y := by
    have t := Real.rpow_le_rpow_of_exponent_le hy hβ2.le
    rwa [Real.rpow_one] at t
  set A := (1 + h) ^ β with hA
  set B := y ^ β with hB
  have hD1 : (1 + β * h - A) * (1 + (1 - β) * h) ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBern hA0]
  have hD2 : 1 + β * h - A ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hD0) (mul_nonneg hq.le hh.le)]
  have key : (y * (1 + h)) * (B / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
      + y * h * (B / β) = -(y * B * ((1 + β * h - A) / (β * (1 - β)))) := by
    rw [hmul]
    field_simp
    ring
  rw [key, abs_neg]
  have hpos : 0 < β * (1 - β) := mul_pos hβ0 hq
  have hE0 : 0 ≤ (1 + β * h - A) / (β * (1 - β)) := div_nonneg (by linarith) hpos.le
  have hE : (1 + β * h - A) / (β * (1 - β)) ≤ h ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hy0 hB0) hE0)]
  have s1 : y * B * ((1 + β * h - A) / (β * (1 - β))) ≤ y * B * h ^ 2 :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hy0 hB0)
  have s2 : y * B * h ^ 2 ≤ y * y * h ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBy hy0) (sq_nonneg h)
  nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg h)]

lemma abs_main_term_second_difference_le {y h γ : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y| ≤ y ^ 2 * h ^ 2 := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hlog : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) :=
    Real.log_mul hy.ne' h1.ne'
  have key : y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y
      = y ^ 2 * ((1 + h) * Real.log (1 + h) - h) := by
    rw [hlog]; ring
  rw [key]
  have hL1 : Real.log (1 + h) ≤ h := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hL2 := le_one_add_mul_log_one_add hh.le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg y) (by linarith))]
  have t : (1 + h) * Real.log (1 + h) - h ≤ h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 h1.le]
  nlinarith [mul_le_mul_of_nonneg_left t (sq_nonneg y)]

lemma exp_neg_sqrt_log_le_sq {cs c₀ y z : ℝ} (hc0 : 0 ≤ c₀) (hcs : c₀ ≤ cs) (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.exp (-cs * Real.sqrt (Real.log z)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ^ 2 := by
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
  have hs : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log z) := Real.sqrt_le_sqrt hlyz
  rw [sq, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul hcs hs (Real.sqrt_nonneg _) (le_trans hc0 hcs)]

end Formalism.ZeroFreeDirichlet
end
end

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma chebyshev_smoothing_identity_complex (ψ Z SY Sy MY My A : ℂ) (y h : ℝ) :
    ((y * h : ℝ) : ℂ) * (ψ + Z)
      = -(((y : ℂ) * SY - ((y * (1 + h) : ℝ) : ℂ) * Sy) - ((y * (1 + h) - y : ℝ) : ℂ) * ψ)
        + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)
        + ((y : ℂ) * (SY - A * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Sy - A * (y : ℂ) + My)) := by
  push_cast; ring

lemma chebyshev_smoothing_identity_real (ψ SY Sy GY Gy y h : ℝ) (hSY : SY = (y * (1 + h)) * Real.log (y * (1 + h))
      - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)) + GY)
    (hSy : Sy = y * Real.log y - (1 + Real.eulerMascheroniConstant) * y + Gy) :
    (y * h) * (ψ - y)
      = -((y * SY - (y * (1 + h)) * Sy) - (y * (1 + h) - y) * ψ)
        + (y * ((y * (1 + h)) * Real.log (y * (1 + h))
            - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)))
          - (y * (1 + h)) * (y * Real.log y - (1 + Real.eulerMascheroniConstant) * y) - y * h * y)
        + (y * GY - (y * (1 + h)) * Gy) := by
  rw [hSY, hSy]; ring

lemma exp_neg_sqrt_log_mem_unit_interval {c₀ y : ℝ} (hc0 : 0 < c₀) :
    0 < Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ∧
      Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  have := mul_nonneg hc0.le (Real.sqrt_nonneg (Real.log y))
  linarith

lemma chebyshev_character_nonprincipal_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (B : Finset ℝ) (hB : ExcZeros c₁ χ B)
    {cs Cs c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hcs : c₀ ≤ cs) (hCs : 0 ≤ Cs) (hy : 2 ≤ y)
    (hE : ∀ z : ℝ, y ≤ z →
      ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        Cs * z * Real.exp (-cs * Real.sqrt (Real.log z))) :
    ‖psiChi χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Cs) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity

  have hβ : ∀ β ∈ B, 1 / 2 ≤ β ∧ β < 1 := by
    intro β hβB
    obtain ⟨_, hreg, hzero, _⟩ := hB.2.1 β hβB
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    simp only [InRegion, Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re] at hreg
    have hl : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlpos : 0 < Real.log ((q : ℝ) * 2) := by linarith
    have hfrac : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hlpos]; linarith
    refine ⟨by linarith, ?_⟩
    by_contra hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by simpa using not_lt.1 hge) hzero
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have hS : ∀ x, Schi χ x = weightedPartialSumUpTo f x := fun x => rfl
  have hP : psiChi χ y = partialSumUpTo f y := rfl
  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  set MY := ∑ β ∈ B, (((y * (1 + h) : ℝ) : ℂ)) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMY
  set My := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMy
  set Z := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ) with hZ
  have hid := chebyshev_smoothing_identity_complex (psiChi χ y) Z (Schi χ (y * (1 + h))) (Schi χ y) MY My (negLD χ 1) y h

  have hM : ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖ ≤
      2 * y ^ 2 * h ^ 2 := by
    have e : ((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z
        = ∑ β ∈ B, (((y * (1 + h) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
            + y * h * (y ^ β / β) : ℝ)) : ℂ) := by
      rw [hMY, hMy, hZ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro β _
      rw [← Complex.ofReal_cpow hypos.le, ← Complex.ofReal_cpow hY0]
      push_cast; ring
    rw [e]
    calc _ ≤ ∑ β ∈ B, ‖(((y * (1 + h) * (y ^ β / (β * (β - 1)))
              - y * ((y * (1 + h)) ^ β / (β * (β - 1))) + y * h * (y ^ β / β) : ℝ)) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ β ∈ B, 2 * y ^ 2 * h ^ 2 := by
          apply Finset.sum_le_sum
          intro β hβB
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_zero_term_second_difference_le (by linarith) hh0 hh1 (hβ β hβB).1 (hβ β hβB).2
      _ = (B.card : ℝ) * (2 * y ^ 2 * h ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * y ^ 2 * h ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hB.1
      _ = 2 * y ^ 2 * h ^ 2 := one_mul _
  have hEY := hE (y * (1 + h)) hyY
  have hEy := hE y le_rfl
  set eY := Real.exp (-cs * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cs * Real.sqrt (Real.log y))
  have hmain : y * h * ‖psiChi χ y + Z‖ ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Cs * (y * (1 + h)) * eY) + y * (1 + h) * (Cs * y * ey) := by
    have hn : ‖((y * h : ℝ) : ℂ) * (psiChi χ y + Z)‖ = y * h * ‖psiChi χ y + Z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hn, hid]
    have hD' : ‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
        - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
        ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
      rw [hS, hS, hP]; exact hD
    have h1 : ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
        ≤ y * (Cs * (y * (1 + h)) * eY) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
      exact mul_le_mul_of_nonneg_left hEY hypos.le
    have h2 : ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖
        ≤ y * (1 + h) * (Cs * y * ey) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0]
      exact mul_le_mul_of_nonneg_left hEy hY0
    calc _ ≤ ‖-(((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y)
            + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)‖
          + ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖ := norm_add_le _ _
      _ ≤ (‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖)
          + (‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖) := by
          gcongr
          · exact (norm_add_le _ _).trans (by rw [norm_neg])
          · exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) hyY
  exact le_of_second_difference_bound hy hc0 hc01 hCs hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain

lemma chebyshev_principal_character_bound {q : ℕ} [NeZero q] {cg Kg c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hcg : c₀ ≤ cg) (hKg : 0 ≤ Kg) (hy : 2 ≤ y)
    (hq : (q : ℝ) ≤ Real.exp (c₀ / 4 * Real.sqrt (Real.log y)))
    (hG : ∀ z : ℝ, y ≤ z → |Formalism.Gz z| ≤ Kg * z * Real.exp (-cg * Real.sqrt (Real.log z))) :
    ‖psiChi (1 : DirichletCharacter ℂ q) y - y‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Kg) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y))
        + 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, le_refl]
  have hS : ∀ x, weightedPartialSumUpTo f x = ((Formalism.Sz x : ℝ) : ℂ) := by
    intro x; simp only [weightedPartialSumUpTo, Formalism.Sz, hf]; push_cast; rfl
  set ψ₀ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n with hψ₀
  have hP : partialSumUpTo f y = ((ψ₀ : ℝ) : ℂ) := by
    simp only [partialSumUpTo, hf, hψ₀]; push_cast; rfl
  set nc := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (if n.Coprime q then 0 else 1) with hnc
  have hpsi : psiChi (1 : DirichletCharacter ℂ q) y = ((ψ₀ - nc : ℝ) : ℂ) := by
    simp only [psiChi, one_apply_natCast, hψ₀, hnc]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp

  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  rw [hS, hS, hP] at hD
  have hD' : |(y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀|
      ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
    have e : ((y : ℂ) * ((Formalism.Sz (y * (1 + h)) : ℝ) : ℂ) - ((y * (1 + h) : ℝ) : ℂ) * ((Formalism.Sz y : ℝ) : ℂ))
        - ((y * (1 + h) - y : ℝ) : ℂ) * ((ψ₀ : ℝ) : ℂ)
        = (((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hD
    exact hD
  have hGY := hG (y * (1 + h)) hyY
  have hGy := hG y le_rfl
  set eY := Real.exp (-cg * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cg * Real.sqrt (Real.log y))
  have hid := chebyshev_smoothing_identity_real ψ₀ (Formalism.Sz (y * (1 + h))) (Formalism.Sz y) (Formalism.Gz (y * (1 + h))) (Formalism.Gz y) y h
    (by simp only [Formalism.Gz]; ring) (by simp only [Formalism.Gz]; ring)
  have hW := abs_main_term_second_difference_le (γ := Real.eulerMascheroniConstant) hypos hh0
  have hmain : y * h * |ψ₀ - y| ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
    rw [← abs_of_pos (show 0 < y * h by positivity), ← abs_mul, hid]
    have h1 : |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y|
        ≤ y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hypos, abs_of_nonneg hY0]
      exact add_le_add (mul_le_mul_of_nonneg_left hGY hypos.le) (mul_le_mul_of_nonneg_left hGy hY0)
    have hsq : 0 ≤ y ^ 2 * h ^ 2 := by positivity
    calc _ ≤ |-((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀)|
          + |y * ((y * (1 + h)) * Real.log (y * (1 + h))
            - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)))
          - (y * (1 + h)) * (y * Real.log y - (1 + Real.eulerMascheroniConstant) * y) - y * h * y|
          + |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y| := abs_add_three _ _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) hyY
  have hfin := le_of_second_difference_bound hy hc0 hc01 hKg hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain

  have hq0 : q ≠ 0 := NeZero.ne q
  have hnc1 := sum_vonMangoldt_not_coprime_le q hq0 ⌊y⌋₊
  rw [← hnc] at hnc1
  have hK : (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ Real.log y := by
    have hfl : ⌊y⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
      omega
    have h2 : ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ y := by
      have := Nat.pow_log_le_self 2 hfl
      calc ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ y := Nat.floor_le hypos.le
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ c₀ / 4 * Real.sqrt (Real.log y) := by
    have := Real.log_le_log (by linarith) hq
    rwa [Real.log_exp] at this
  have hncb := mul_le_of_log_bounds hy hc0 hc01 hK (by positivity) hlq0 hlq
  have hnc0 : 0 ≤ nc := Finset.sum_nonneg fun n _ =>
    mul_nonneg vonMangoldt_nonneg (by split_ifs <;> norm_num)
  rw [hpsi]
  have e : ((ψ₀ - nc : ℝ) : ℂ) - (y : ℂ) = (((ψ₀ - y) - nc : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  calc |(ψ₀ - y) - nc| ≤ |ψ₀ - y| + |nc| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hnc0]; linarith

theorem chebyshev_character_bound_of : PsiChiBoundOf := by
  intro hS hG c₁ hc₁ hc₁'
  obtain ⟨cs, Cs, hcs, hSm⟩ := hS c₁ hc₁ hc₁'
  obtain ⟨cg, Kg, hcg, hGz⟩ := hG
  set c₀ := min (min cs cg) 1 with hc0def
  have hc0 : 0 < c₀ := lt_min (lt_min hcs hcg) one_pos
  have hc01 : c₀ ≤ 1 := min_le_right _ _
  have hc0s : c₀ ≤ cs := (min_le_left _ _).trans (min_le_left _ _)
  have hc0g : c₀ ≤ cg := (min_le_left _ _).trans (min_le_right _ _)
  set Cs' := max Cs 0
  set Kg' := max Kg 0
  refine ⟨c₀ / 4, 128 / c₀ ^ 2 + 2 + 4 * Cs' + 4 * Kg' + 16, by positivity, ?_⟩
  intro q _ χ B x hB hx hq
  have he4 : 0 ≤ x * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log x)) := by positivity
  have hCs' : 0 ≤ Cs' := le_max_right _ _
  have hKg' : 0 ≤ Kg' := le_max_right _ _
  by_cases hχ : χ = 1
  · have hB0 : B = ∅ := Finset.eq_empty_of_forall_notMem fun β hβ => (hB.2.1 β hβ).1 hχ
    subst hχ hB0
    rw [if_pos rfl, Finset.sum_empty, add_zero]
    have hG' : ∀ z : ℝ, x ≤ z → |Formalism.Gz z| ≤ Kg' * z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
      intro z hz
      refine (hGz z (by linarith)).trans ?_
      have : 0 ≤ z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Kg 0]
    have := chebyshev_principal_character_bound (q := q) hc0 hc01 hc0g hKg' hx hq hG'
    nlinarith
  · rw [if_neg hχ, sub_zero]
    have hE : ∀ z : ℝ, x ≤ z →
        ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
          Cs' * z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
      intro z hz
      have hqz : (q : ℝ) ≤ Real.exp (cs * Real.sqrt (Real.log z)) := by
        refine hq.trans (Real.exp_le_exp.2 ?_)
        have h1 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hz)
        have h0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
        have h0' : 0 ≤ Real.sqrt (Real.log z) := Real.sqrt_nonneg _
        nlinarith
      refine (hSm q χ B z hχ hB (by linarith) hqz).trans ?_
      have : 0 ≤ z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Cs 0]
    have := chebyshev_character_nonprincipal_bound χ hχ hc₁ hc₁' B hB hc0 hc01 hc0s hCs' hx hE
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.FinalSiegel
namespace Formalism.ZeroFreeDirichlet

theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet
end

namespace Formalism.ZeroFreeDirichlet

theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet
