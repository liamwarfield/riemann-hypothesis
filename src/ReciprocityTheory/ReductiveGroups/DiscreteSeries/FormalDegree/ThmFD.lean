module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConst
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ThmFD

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpper
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperB
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_hs_smul {ε : Fin n → Bool} (s : ℝ) (y : PCoord ε → ℂ) :
    hs (pmat ((s : ℂ) • y)) = s ^ 2 * hs (pmat y) := by
  have hp : pmat ((s : ℂ) • y) = (s : ℂ) • pmat y := by
    ext a b
    simp only [pmat, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [star_mul', Complex.conj_ofReal]
  rw [hp]
  unfold hs
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem fdU_hs_nonneg {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 ≤ hs (pmat y) := by
  unfold hs
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

theorem fdU_sqrt_hs_smul {ε : Fin n → Bool} {s : ℝ} (hs0 : 0 ≤ s) (y : PCoord ε → ℂ) :
    Real.sqrt (hs (pmat ((s : ℂ) • y))) = s * Real.sqrt (hs (pmat y)) := by
  rw [fdU_hs_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs0]

theorem fdU_qf_smul {ε : Fin n → Bool} (lam : Fin n → ℝ) (s : ℝ) (y : PCoord ε → ℂ) :
    Qf lam ((s : ℂ) • y) = s ^ 2 * Qf lam y := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem fdU_antitone_zero : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl

theorem fdU_ph_ge {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ) (z : PCoord ε → ℂ) :
    (t : ℝ) * Ph (0 : Fin n → ℝ) (pmat z) ≤ Ph (lamT lam t) (pmat z) := by
  rw [ph_lamT]
  linarith [ph_nonneg hlam z]

theorem fdU_near {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {s : ℝ} (hs0 : 0 < s) {t : ℕ}
    (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) (hr : s * rhoP y ≤ 1) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp (-(1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (s * Real.sqrt (hs (pmat y)))) := by
  have hrho : rhoP ((s : ℂ) • y) = s * rhoP y := by rw [rhoP_real_smul, abs_of_pos hs0]
  have hl := ph_lower (lam := (0 : Fin n → ℝ)) fdU_antitone_zero ((s : ℂ) • y) (ep := s * rhoP y) hrho.le hr
  rw [fdU_qf_smul] at hl
  have hg := fdU_ph_ge hlam t ((s : ℂ) • y)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hQ : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y =
      (t : ℝ) * ((1 - s * rhoP y) * (s ^ 2 * Qf (0 : Fin n → ℝ) y)) := by
    calc _ = (s ^ 2 * t) * ((1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y) := by rw [hst]; ring
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hl ht
  have h1 : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y ≤ 2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) := by
    rw [hQ]; linarith
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  rw [Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hJ (le_trans zero_le_one (jac_ge_one _))
    (Real.exp_pos _).le

theorem fdU_far {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {t₀ t : ℕ} (h0 : 1 ≤ t₀)
    (ht : t₀ ≤ t) {s : ℝ} (hs0 : 0 < s) (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp ((Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32 -
        (Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt t₀) * Real.sqrt (hs (pmat y))) := by
  have hhs : hs (pmat y) = Real.sqrt (hs (pmat y)) ^ 2 := (Real.sq_sqrt (fdU_hs_nonneg y)).symm
  have hm := potential_lower_min ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le, fdU_hs_smul] at hm
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  have hPh := fdU_ph_ge hlam t ((s : ℂ) • y)
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set r := Real.sqrt (hs (pmat y)) with hr
  set X := Real.sqrt (t₀ : ℝ) with hX
  set a := X / k with ha
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hT0 : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast h0)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hsT : s * X ≤ 1 := by
    have h1 : s ^ 2 * t₀ ≤ 1 := by
      rw [← hst]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (sq_nonneg s)
    have h2 : (s * X) ^ 2 ≤ 1 := by rw [mul_pow, hX, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h1
    nlinarith [mul_pos hs0 hT0]
  have hsinv : X ≤ s⁻¹ := by
    calc X = s⁻¹ * (s * X) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left hsT (inv_nonneg.mpr hs0.le)
      _ = s⁻¹ := mul_one _
  have hmin : a * r - a ^ 2 / 4 ≤ (t : ℝ) * min (s ^ 2 * hs (pmat y)) (s * r / k) := by
    rw [mul_min_of_nonneg _ _ ht0]
    refine le_min ?_ ?_
    · have e : (t : ℝ) * (s ^ 2 * hs (pmat y)) = r ^ 2 := by
        rw [hhs]; linear_combination r ^ 2 * hst
      rw [e]; nlinarith [sq_nonneg (r - a / 2)]
    · have hrk : 0 ≤ r / k := div_nonneg hr0 hk0
      have e : (t : ℝ) * (s * r / k) = s⁻¹ * (r / k) := by
        have : s⁻¹ = s * t := by field_simp; linear_combination -hst
        rw [this]; ring
      have ea : a * r = X * (r / k) := by rw [ha]; ring
      rw [e]; nlinarith [mul_le_mul_of_nonneg_right hsinv hrk, sq_nonneg a]
  have hs' : s ≤ 1 / X := by rw [le_div_iff₀ hT0]; exact hsT
  have hJ2 : ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k / X * r := by
    calc ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k * (s * r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hk0) (by positivity)
      _ ≤ |(n : ℝ) - 1| * k * (1 / X * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs' hr0) (by positivity)
      _ = _ := by ring
  have hm2 := mul_le_mul_of_nonneg_left hm ht0
  have hE : -2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) ≤ a ^ 2 / 32 - a / 8 * r := by
    nlinarith
  calc Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y)
      ≤ Real.exp (a ^ 2 / 32 - a / 8 * r) * Real.exp (|(n : ℝ) - 1| * k / X * r) :=
        mul_le_mul (Real.exp_le_exp.mpr hE) (hJ.trans (Real.exp_le_exp.mpr hJ2))
          (le_trans zero_le_one (jac_ge_one _)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem one_le_q0_of_coord {ε : Fin n → Bool} (ab : PCoord ε) : 1 ≤ q0 ε := by
  unfold q0 pOf qOf
  have h := ab.2.2
  have ht : ε ab.1.1 = true ∨ ε ab.1.2 = true := by
    cases h1 : ε ab.1.1 <;> cases h2 : ε ab.1.2 <;> simp_all
  have hf : ε ab.1.1 = false ∨ ε ab.1.2 = false := by
    cases h1 : ε ab.1.1 <;> cases h2 : ε ab.1.2 <;> simp_all
  apply le_min
  · rcases ht with h1 | h1
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
  · rcases hf with h1 | h1
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩

theorem fdU_c_pos {ε : Fin n → Bool} (ab : PCoord ε) :
    0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
  have hQ : (1 : ℝ) ≤ q0 ε := by exact_mod_cast one_le_q0_of_coord ab
  have hn : (1 : ℝ) ≤ n := by
    have := ab.1.1.isLt
    exact_mod_cast (show 1 ≤ n by omega)
  have hA : (((16 * n * q0 ε + 1 : ℕ) : ℝ)) = 16 * n * q0 ε + 1 := by push_cast; ring
  rw [hA, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n - 1)]
  have ha : 0 < Real.sqrt (16 * n * q0 ε + 1) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < Real.sqrt (2 * (q0 ε : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have ha2 : Real.sqrt (16 * n * q0 ε + 1) ^ 2 = 16 * n * q0 ε + 1 := Real.sq_sqrt (by positivity)
  have hb2 : Real.sqrt (2 * (q0 ε : ℝ)) ^ 2 = 2 * q0 ε := Real.sq_sqrt (by positivity)
  have key : Real.sqrt (16 * n * q0 ε + 1) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt (16 * n * q0 ε + 1) =
      (Real.sqrt (16 * n * q0 ε + 1) ^ 2 - 8 * ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) ^ 2) /
        (8 * Real.sqrt (16 * n * q0 ε + 1) * Real.sqrt (2 * (q0 ε : ℝ))) := by
    field_simp
  rw [key, ha2, hb2]
  apply div_pos _ (by positivity)
  nlinarith

theorem fdU_exp_le_prod {ε : Fin n → Bool} {c : ℝ} (hc : 0 ≤ c) (y : PCoord ε → ℂ) :
    Real.exp (-c * Real.sqrt (hs (pmat y))) ≤
      ∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) := by
  rw [show (∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) =
      Real.exp (∑ ab : PCoord ε, -(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) from
      (Real.exp_sum _ _).symm, Real.exp_le_exp]
  have hent : ∀ ab : PCoord ε, ‖y ab‖ ≤ Real.sqrt (hs (pmat y)) := by
    intro ab
    have hpm : pmat y ab.1.1 ab.1.2 = y ab := by
      simp only [pmat]
      rw [dite_eq_left ab.2]
    have h2 : ‖y ab‖ ^ 2 ≤ hs (pmat y) := by
      unfold hs
      calc ‖y ab‖ ^ 2 = ‖pmat y ab.1.1 ab.1.2‖ ^ 2 := by rw [hpm]
        _ ≤ ∑ j, ‖pmat y ab.1.1 j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖pmat y ab.1.1 j‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ _)
        _ ≤ ∑ i, ∑ j, ‖pmat y i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j, ‖pmat y i j‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ _)
    calc ‖y ab‖ = |‖y ab‖| := (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hs (pmat y)) := Real.abs_le_sqrt h2
  have hsq := Real.sqrt_nonneg (hs (pmat y))
  have hsum : ∑ ab : PCoord ε, ‖y ab‖ ≤ ((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y)) := by
    calc ∑ ab : PCoord ε, ‖y ab‖ ≤ ∑ ab : PCoord ε, Real.sqrt (hs (pmat y)) :=
          Finset.sum_le_sum (fun ab _ => hent ab)
      _ = (Fintype.card (PCoord ε) : ℝ) * Real.sqrt (hs (pmat y)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y)) := by linarith
  rw [← Finset.mul_sum]
  have hN : (0 : ℝ) < (Fintype.card (PCoord ε) : ℝ) + 1 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hsum (div_nonneg hc hN.le)
  have e : c / ((Fintype.card (PCoord ε) : ℝ) + 1) *
      (((Fintype.card (PCoord ε) : ℝ) + 1) * Real.sqrt (hs (pmat y))) = c * Real.sqrt (hs (pmat y)) := by
    field_simp
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_s_pos {t : ℕ} (ht : 1 ≤ t) : 0 < (Real.sqrt (t : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))

theorem fdU_s_sq {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := by
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr (by omega)
  rw [inv_pow, Real.sq_sqrt ht'.le, inv_mul_cancel₀ ht'.ne']

theorem fdU_major {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ)
    (ht : 16 * n * q0 ε + 1 ≤ t) (y : PCoord ε → ℂ) :
    ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) ≤
      ENNReal.ofReal (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32) *
        ∏ ab : PCoord ε, Real.exp (-((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) := by
  have ht1 : 1 ≤ t := le_trans (by omega) ht
  have hs0 := fdU_s_pos ht1
  have hst := fdU_s_sq ht1
  have hfar := fdU_far hlam (t₀ := 16 * n * q0 ε + 1) (by omega) ht hs0 hst y
  apply ENNReal.ofReal_le_ofReal
  refine hfar.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rcases isEmpty_or_nonempty (PCoord ε) with hE | hN
  · have hp : pmat y = 0 := by
      ext a b
      simp only [pmat, Matrix.zero_apply]
      split_ifs with h1 h2
      · exact (hE.false ⟨(a, b), h1⟩).elim
      · exact (hE.false ⟨(b, a), h2⟩).elim
      · rfl
    have hh : hs (pmat y) = 0 := by rw [hp]; simp [hs]
    rw [hh, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]
    simp
  · have ab : PCoord ε := Classical.choice hN
    have hc := fdU_c_pos ab
    have h2 := fdU_exp_le_prod hc.le y
    rw [← neg_mul]
    exact h2

theorem fdU_pointwise {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (T : ℕ) (hT : 1 ≤ T)
    (y : PCoord ε → ℂ) :
    limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop ≤
      ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
  set ρ := rhoP y
  set r := Real.sqrt (hs (pmat y))
  set C := ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ))
  set φ : ℝ → ℝ := fun v => Real.exp (-(1 - v * ρ) * Qf (0 : Fin n → ℝ) y + C * (v * r)) with hφdef
  have hφ : Continuous φ := by
    simp only [hφdef]; fun_prop
  have hu : Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)))
  have hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * ρ < 1 := by
    have h := hu.mul_const ρ
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds one_pos)
  have hle : ∀ᶠ t : ℕ in atTop, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)) ≤
        ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) :=
    hev.mono fun t ht => ENNReal.ofReal_le_ofReal
      (fdU_near hlam (fdU_s_pos (by omega)) (fdU_s_sq (by omega)) y ht.le)
  have hlim : Tendsto (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (φ 0))) :=
    ENNReal.tendsto_ofReal ((hφ.tendsto 0).comp hu)
  have h0 : φ 0 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by simp [hφdef]
  calc _ ≤ limsup (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop :=
        limsup_le_limsup hle
    _ = ENNReal.ofReal (φ 0) := hlim.limsup_eq
    _ = _ := by rw [h0]

theorem formal_degree_limsup_upper_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) :
    Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) Filter.atTop ≤
      ENNReal.ofReal (PiW ε 0) := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  set T : ℕ := 16 * n * q0 ε + 1 with hT
  rw [← Filter.limsup_nat_add _ T]
  refine le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
      (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) :=
      continuous_const_smul _
    exact (Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul
      ((jac_continuous ε).comp hc)
  have hint := ((fdU_integrable_prod_exp (ε := ε)
    (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1))
    (fun ab => div_pos (fdU_c_pos ab) (by positivity))).const_mul
    (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32)))
  calc _ ≤ ∫⁻ y, limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop :=
        limsup_lintegral_le _ hmeas
          (fun t => Filter.Eventually.of_forall fun y => fdU_major hlam (t + T) (by omega) y)
          hint.lintegral_lt_top.ne
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) :=
        lintegral_mono fun y => fdU_pointwise hlam T (by omega) y
    _ = _ := fdU_lintegral_gauss ε

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLower
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by

  have hsq : ∀ y : PCoord ε → ℂ,
      ‖(((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2))) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
    intro y
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 1
    ring
  have htend : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    intro y
    rw [← hsq y]
    exact ENNReal.tendsto_ofReal (((hlim y).norm).pow 2)
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) := by
    intro t
    exact ENNReal.measurable_ofReal.comp
      ((((fdl_inner_continuous (lamT lam t) (T t) (T t).w (T t).w).comp
        (continuous_const_smul _)).norm.pow 2).measurable)
  have key : ∀ t : ℕ, 1 ≤ t →
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
        (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2) ≤
      ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
    have hs : (0 : ℝ) < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
    have hpow : ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = ((t : ℝ) ^ (pOf ε * qOf ε))⁻¹ := by
      rw [pow_mul, inv_pow, Real.sq_sqrt ht0.le, inv_pow]
    conv_rhs => rw [lintegral_pcoord_smul _ hs]
    try rw [show 2 * pOf ε * qOf ε = 2 * (pOf ε * qOf ε) from mul_assoc _ _ _]
    rw [hpow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_mul]
    refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)
  calc ENNReal.ofReal (PiW ε 0)
      = ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := (fdl_gauss ε).symm
    _ = ∫⁻ y : PCoord ε → ℂ, Filter.liminf (fun t : ℕ => ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := by
        congr 1
        funext y
        rw [(htend y).liminf_eq]
    _ ≤ Filter.liminf (fun t : ℕ => ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ _ := by
        refine Filter.liminf_le_liminf ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with t ht using key t ht

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdPointwise
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem trace_dMat_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) : trace (Lap.Base.dMat (Dvec n) * pmat y) = 0 := by
  simp only [Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [pmat]

theorem pmat_herm_apply {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    pmat y b a = star (pmat y a b) := by
  simp only [pmat]
  by_cases h1 : a < b ∧ ε b ≠ ε a
  · have h2 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => lt_asymm h.1 h1.1
    simp only [dif_pos h1, dif_neg h2, star_star]
  · by_cases h2 : b < a ∧ ε a ≠ ε b
    · simp only [dif_neg h1, dif_pos h2]
    · simp only [dif_neg h1, dif_neg h2, star_zero]

theorem sum_pairs_pmat_fp {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := _root_.ReciprocityTheory.ChartRestriction.DS.G2.sum_pairs_pmat_fp (ε := ε) w z

private theorem pmat_apply_eq_zero_of_sign_eq {ε : Fin n → Bool} (y : PCoord ε → ℂ) {a b : Fin n} (he : ε a = ε b) :
    pmat y a b = 0 := by
  simp only [pmat]
  rw [dif_neg (fun h => h.2 he), dif_neg (fun h => h.2 he.symm)]

theorem qForm_term {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
      (((if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ)) : ℂ) := by
  have hD : ((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ) = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp only [Dvec]; push_cast; ring
  by_cases h : b < a ∧ ε a ≠ ε b
  · have hin : Lap.Base.InNM ε (Dvec n) b a := Or.inr h
    have hN : Lap.Base.partNM ε (Dvec n) (pmat y) b a = pmat y b a := by
      rw [Lap.Base.partNM, Matrix.of_apply, if_pos hin]
    rw [hN, if_pos h.1, hD, pmat_herm_apply y a b, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  · have h0 : pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a = 0 := by
      rw [Lap.Base.partNM, Matrix.of_apply]
      split_ifs with hin
      · rcases hin with ⟨_, he, _⟩ | h'
        · rw [pmat_apply_eq_zero_of_sign_eq y he, zero_mul]
        · exact absurd h' h
      · exact mul_zero _
    rw [h0, mul_zero, neg_zero]
    split_ifs with hba
    · have he : ε a = ε b := by
        by_contra he
        exact h ⟨hba, he⟩
      rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · simp

theorem qForm_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Lap.Base.qForm ε (Dvec n) (pmat y) = ((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) := by
  have h1 : Lap.Base.qForm ε (Dvec n) (pmat y) = ∑ a : Fin n, ∑ b : Fin n,
      -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) := by
    have e : ∀ a b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
        -(((Dvec n a : ℝ) : ℂ) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) +
          ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b) :=
      fun a b => by ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_comm (f := fun a b : Fin n =>
      ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b))]
    simp only [Lap.Base.qForm, Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [h1]
  simp only [qForm_term]
  have e2 := sum_pairs_pmat_fp (fun a b : Fin n => ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) y
  rw [Fintype.sum_prod_type' (f := fun a b : Fin n =>
    (if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ))] at e2
  rw [← Complex.ofReal_inj] at e2
  simp only [Complex.ofReal_sum] at e2
  rw [e2, ← Complex.ofReal_sum]
  congr 1
  simp only [Qf, wab, Pi.zero_apply, sub_self, zero_add]

theorem matrix_coefficient_pointwise_limit (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} (H : ℕ → Type)
    [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (y : PCoord ε → ℂ) :
    Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hB3 n ε (Dvec n) (lowK ε lam) (S7.hs (pmat y) + 1)
  have hinG : inG ε (pmat y) := by
    unfold inG Jm
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    rw [pmat_herm_apply y a b, star_star]
    by_cases he : ε a = ε b
    · rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · cases ha : ε a <;> cases hb : ε b <;> simp_all
  have hR : S7.hs (pmat y) ≤ (S7.hs (pmat y) + 1) ^ 2 := by
    nlinarith [sq_nonneg (S7.hs (pmat y) + 1 / 2)]
  have hsq : Filter.Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨⌈b ^ 2⌉₊, fun a ha => ?_⟩
    refine (le_abs_self b).trans (Real.abs_le_sqrt ?_)
    exact (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have hC0 : Filter.Tendsto (fun t : ℕ => C / Real.sqrt (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hC0
  filter_upwards [hsm, Filter.eventually_ge_atTop 1] with t ht ht1
  obtain ⟨H', i1, i2, σ', w', hw', heq⟩ := ht
  letI := i1
  letI := i2
  have hlow : lowK ε (lamT lam t) = (t : ℝ) • Dvec n + lowK ε lam := by
    ext a
    simp only [lowK, lamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb := hC (t : ℝ) (by exact_mod_cast ht1) H' σ' (lamT lam t) w' hw' hlow (pmat y) hinG hR
  rw [trace_dMat_pmat y, qForm_pmat y, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hb
  have hy : ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y) = ((Real.sqrt t)⁻¹ : ℝ) • y := by
    ext ab
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  have hL : (((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) =
      Complex.exp (-((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) / 2) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [← heq, hy, adKAux_pmat_smul, hL]
  exact hb

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdStep
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact add_lt_add_of_lt_of_le (hlam hij) (by exact_mod_cast hc hij.le)

theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  unfold IsHCParam at hlam ⊢
  refine ⟨fdS_strictAnti hlam.1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  unfold GapAtLeast at hgap ⊢
  intro a b hab
  have h0 := hgap a b hab
  simp only [Pi.add_apply]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 := hlam hlt
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc hlt.le
    rw [abs_of_pos (by linarith)] at h0
    rw [abs_of_pos (by linarith)]
    linarith
  · exact absurd (congrArg ε heq) hab
  · have h1 := hlam hgt
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc hgt.le
    rw [abs_of_neg (by linarith)] at h0
    rw [abs_of_neg (by linarith)]
    linarith

private theorem vand_ne_zero_of_strictAnti {μ : Fin n → ℝ} (hμ : StrictAnti μ) : Vand μ ≠ 0 := by
  unfold Vand
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_ne_zero.mpr (hμ hab).ne'

theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμ1 : StrictAnti μ := by unfold IsHCParam at hμ; exact hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμ1 s]
  have h1 := vand_ne_zero_of_strictAnti hμ1
  have h2 := vand_ne_zero_of_strictAnti hs
  field_simp

theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  have hlam1 : StrictAnti lam := by unfold IsHCParam at hlam; exact hlam.1
  intro N
  induction N with
  | zero =>
    intro c _ hsum
    have hc0 : ∀ i, c i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    have hfun : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [hc0 i]
    rw [hfun]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have h0 : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i hi => by simpa using hemp hi)
      omega
    obtain ⟨s, hs_mem, hs_max⟩ : ∃ s ∈ univ.filter (fun i => c i ≠ 0), ∀ j ∈ univ.filter (fun i => c i ≠ 0), j ≤ s :=
      ⟨_, Finset.max'_mem _ hne, fun j hj => Finset.le_max' _ j hj⟩
    have hcs : c s ≠ 0 := (Finset.mem_filter.mp hs_mem).2
    have hbig : ∀ j, s < j → c j = 0 := by
      intro j hj
      by_contra hcj
      exact absurd hj (not_lt.mpr (hs_max j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)))
    set c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i with hc'_def
    have hcc : ∀ i, c i = c' i + (if i = s then 1 else 0) := by
      intro i
      simp only [hc'_def]
      by_cases h : i = s
      · rw [if_pos h, if_pos h, h]; omega
      · rw [if_neg h, if_neg h]; rfl
    have hc' : Antitone c' := by
      intro i j hij
      simp only [hc'_def]
      rcases eq_or_ne i s with hi | hi <;> rcases eq_or_ne j s with hj | hj
      · rw [hi, hj]
      · have hsj : s < j := lt_of_le_of_ne (hi ▸ hij) (Ne.symm hj)
        rw [if_neg hj, hbig j hsj]
        exact Nat.zero_le _
      · have h' := hc hij
        rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hc hij
    have hsum' : ∑ i, c' i = N := by
      have h' : ∑ i, c i = ∑ i, c' i + 1 := by
        rw [Finset.sum_congr rfl (fun i _ => hcc i), Finset.sum_add_distrib]
        simp
      omega
    have hfun : (lam + fun i => (c' i : ℝ)) + Pi.single s 1 = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply]
      rw [hcc i]
      push_cast
      split_ifs <;> ring
    have hQ := fdS_stepQ dfun hstep (fdS_hc hlam hc') (fdS_gap hlam1 hgap hc') s
      (by rw [hfun]; exact fdS_gap hlam1 hgap hc) (by rw [hfun]; exact fdS_strictAnti hlam1 hc)
    rw [hfun] at hQ
    rw [hQ, ih c' hc' hsum']

theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hD : ∀ a : Fin n, ((n : ℝ) - 1) - ((a : ℕ) : ℝ) = ((n - 1 - (a : ℕ) : ℕ) : ℝ) := by
    intro a
    have ha := a.2
    rw [Nat.cast_sub (by omega : (a : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hc : Antitone (fun a : Fin n => t * (n - 1 - (a : ℕ))) := by
    intro i j hij
    have h' := Fin.le_iff_val_le_val.mp hij
    exact Nat.mul_le_mul le_rfl (by omega)
  have hfun : lamT lam t = lam + fun i => (((fun a : Fin n => t * (n - 1 - (a : ℕ))) i : ℕ) : ℝ) := by
    funext i
    simp only [lamT, Pi.add_apply, Pi.smul_apply, Dvec, smul_eq_mul]
    rw [hD i]
    push_cast
    ring
  rw [hfun]
  exact fdS_main dfun hstep hlam hgap _ _ hc rfl

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem thmFD (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hp : 1 ≤ pOf ε)
    (hq : 1 ≤ qOf ε) (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h)
    (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    (H : ℕ → Type) [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (hd : ∀ᶠ t in Filter.atTop, Formalism.MainNotions.S.IsFdeg (muCD ε) (σ t) (dfun (lamT lam t))) :
    dfun lam = dimVlam lam := by
  have hlam0 : lamT lam 0 = lam := by simp [lamT]
  have hanti : Antitone lam := hlam.1.antitone
  have hcP : 0 < cPQ ε := lt_of_lt_of_le (inv_pos.mpr (pow_pos Real.pi_pos _)) (inv_pi_pow_le_cPQ ε)
  have hpos : ∀ t, (0:ℝ) < Module.finrank ℂ (T t).V := fun t => by
    have : Nontrivial (T t).V := ⟨⟨(T t).w, 0, fun h => by
      have h2 := (T t).w_norm
      rw [h, norm_zero] at h2
      exact zero_ne_one h2⟩⟩
    exact_mod_cast Module.finrank_pos
  have h1 : ∀ t, dfun (lamT lam t) / Vand (lamT lam t) = dfun (lamT lam 0) / Vand lam := fun t => by
    rw [hlam0]; exact fd_step dfun hstep hlam hgap t
  have hd0 : 0 < dfun (lamT lam 0) := by
    obtain ⟨t, ht⟩ := hd.exists
    have hv1 : 0 < Vand (lamT lam t) := vand_pos (isHCParam_lamT hlam t).1
    have hv0 : 0 < Vand lam := vand_pos hlam.1
    have e : dfun (lamT lam 0) = Vand lam * (dfun (lamT lam t) / Vand (lamT lam t)) := by
      rw [h1 t]; field_simp
    rw [e]
    have := ht.1
    positivity
  have hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0) := by
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
        (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) ≤ ENNReal.ofReal (cPQ ε) *
        (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
          ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have L6 := lemma6c hFt hdt
      have hdt0 := hdt.1
      have hD := hpos t
      have hA : 0 ≤ (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) := by positivity
      calc ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))
          = ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              ENNReal.ofReal (1 / dfun (lamT lam t)) := by
            rw [← ENNReal.ofReal_mul hA]; congr 1; ring
        _ ≤ ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              (ENNReal.ofReal (cPQ ε / Module.finrank ℂ (T t).V) *
                ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
            gcongr
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
            have e2 : (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) *
                (cPQ ε / Module.finrank ℂ (T t).V) = cPQ ε * (t:ℝ) ^ (pOf ε * qOf ε) := by
              field_simp
            rw [e2, ENNReal.ofReal_mul hcP.le, mul_assoc]
    refine le_trans (Filter.limsup_le_limsup hev) ?_
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
    exact formal_degree_limsup_upper_bound hanti
  have hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop := by
    have hL := formal_degree_liminf_lower_bound T (matrix_coefficient_pointwise_limit hB3 H σ T j hF hsm)
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) ≤
        ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have F3 := lintegral_fF_coeff_sq_le_finrank_div_fdeg hFt hdt
      calc _ = ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) * (ENNReal.ofReal (cPQ ε) *
            ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) := by
            ring
        _ ≤ ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
              ENNReal.ofReal ((Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_div_assoc]
    refine le_trans ?_ (Filter.liminf_le_liminf hev)
    rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
  have := formal_degree_constant_eq hlam (fun t => dfun (lamT lam t)) T h1 hd0 hup hlow
  simpa only [hlam0] using this

end ReciprocityTheory.ChartRestriction.DS
