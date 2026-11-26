module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.VarZeroSubVarOneNe
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.ThirdRootSubVarZeroNeZero
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffWSeriesVarZero
noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem lamA_coeff_wser (wq : PowerSeries ℂ_[p]) (n : ℕ) :
    PowerSeries.coeff n (wser wq) = if 3 ≤ n then PowerSeries.coeff (n - 3) wq else 0 := by
  simp [wser, PowerSeries.coeff_X_pow_mul']

theorem lamA_coeff_lam (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam wq) = PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) := rfl

theorem lamA_single0 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem lamA_single1 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem coeff_wSeriesVar_zero (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 0) = if e 1 = 0 then PowerSeries.coeff (e 0) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single0 e) rfl rfl

theorem coeff_wSeriesVar_one (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 1) = if e 0 = 0 then PowerSeries.coeff (e 1) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single1 e) rfl rfl

theorem lamA_coeff_mul_X (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by
  rw [Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

theorem lam_mul (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X,
    coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]
  have a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0 := by simp
  have a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1 := by simp
  have a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1 := by simp
  have a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1 := by simp
  rw [a1, a2, a3, a4]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · simp [h0, h1]
  · have : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    simp [h0, h1, this]
  · have : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e 0 - 1 + 0 + 1 = e 0 := by omega
    simp [h0, h1, this, h2]
  · have h3 : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h4 : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    have h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1 := by omega
    simp [h0, h1, h3, h4, h2]

theorem wv_line1 (wq : PowerSeries ℂ_[p]) : wv wq 1 = lam wq * Xv 1 + nu wq := by
  have h := lam_mul wq
  simp only [nu]
  linear_combination -h

theorem constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]
  simp

theorem lamA_wser_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by
  rw [lamA_coeff_wser]; split_ifs
  · exact hS _
  · exact S.zero_mem

theorem lam_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by
  intro e
  rw [lamA_coeff_lam]
  exact lamA_wser_mem hS _

theorem G_wv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (i : Fin 2) :
    G W (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wv wq i) = 0 := by
  have hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.X i
  set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ
  have hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X := by
    rw [hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  have hw : wv wq i = φ (wser wq) := by
    rw [hφ, PowerSeries.coe_substAlgHom]; rfl
  rw [hX, hw]
  have : G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq)) := by
    simp only [G, map_add (f := _), map_sub, map_mul, map_pow, AlgHom.commutes]
  rw [this, G_wser h, map_zero]

end PI.AddIntG.Wk
end
end

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

section order

variable {σ : Type*}

theorem rt_two_le_mul_left (f g : MvPowerSeries σ ℂ_[p]) (hg : 2 ≤ g.order) : 2 ≤ (f * g).order := by
  first
    | exact (hg.trans le_add_self).trans (MvPowerSeries.le_order_mul ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.add_order_le_order_mul ..)

theorem rt_two_le_mul_right (f g : MvPowerSeries σ ℂ_[p]) (hf : 2 ≤ f.order) : 2 ≤ (f * g).order := by
  first
    | exact (hf.trans le_self_add).trans (MvPowerSeries.le_order_mul ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.add_order_le_order_mul ..)

theorem rt_two_le_add {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f + g).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [map_add (f := _), MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
    MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]

theorem rt_two_le_neg {f : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) : 2 ≤ (-f).order := by
  rw [MvPowerSeries.order_neg]
  exact hf

theorem rt_two_le_sub {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f - g).order := by
  rw [sub_eq_add_neg]
  exact rt_two_le_add hf (rt_two_le_neg hg)

theorem rt_one_le_X (i : σ) : 1 ≤ (Xv i : MvPowerSeries σ ℂ_[p]).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [MvPowerSeries.coeff_X, if_neg]
  rintro rfl
  simp at hd

theorem rt_two_le_mul_X {f : MvPowerSeries σ ℂ_[p]} (hf : 1 ≤ f.order) (i : σ) :
    2 ≤ (f * Xv i).order := by
  have h2 : (2 : ℕ∞) ≤ f.order + (Xv i : MvPowerSeries σ ℂ_[p]).order :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add hf (rt_one_le_X i)
  first
    | exact h2.trans (MvPowerSeries.le_order_mul ..)
    | exact h2.trans (MvPowerSeries.order_mul_ge ..)
    | exact h2.trans (MvPowerSeries.add_order_le_order_mul ..)

end order

theorem rt_order_lam (wq : PowerSeries ℂ_[p]) : 2 ≤ (lam wq).order := by
  refine MvPowerSeries.le_order fun e he => ?_
  have hd : e 0 + e 1 < 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at he
    exact_mod_cast he
  rw [lamA_coeff_lam, lamA_coeff_wser, if_neg (by omega)]

private theorem rt_constantCoeff_lam_lemma {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : 2 ≤ f.order) :
    MvPowerSeries.constantCoeff f = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ hf
  simp

theorem rt_constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  exact rt_constantCoeff_lam_lemma (rt_order_lam wq)

theorem rt_wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    wv wq i = (Xv i) ^ 3 * PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) wq := by
  have ha : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  unfold wv wser
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha]

theorem rt_order_nu (wq : PowerSeries ℂ_[p]) : 2 ≤ (nu wq).order := by
  have h3 : 2 ≤ ((Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 3).order := by
    rw [pow_succ]
    exact rt_two_le_mul_right _ _ (by rw [pow_two]; exact rt_two_le_mul_X (rt_one_le_X 0) 0)
  unfold nu
  rw [rt_wv]
  exact rt_two_le_sub (rt_two_le_mul_right _ _ h3) (rt_two_le_mul_right _ _ (rt_order_lam wq))

theorem rt_constantCoeff_nu (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (nu wq) = 0 := by
  exact rt_constantCoeff_lam_lemma (rt_order_nu wq)

theorem rt_order_Bcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : 2 ≤ (Bcf W wq).order := by
  unfold Bcf
  have hl := rt_order_lam wq
  have hn := rt_order_nu wq
  have hl2 : 2 ≤ (lam wq ^ 2).order := by rw [pow_two]; exact rt_two_le_mul_left _ _ hl
  refine rt_two_le_add (rt_two_le_add (rt_two_le_add (rt_two_le_add ?_ ?_) ?_) ?_) ?_
  · exact rt_two_le_mul_left _ _ hl
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hl2
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hn

theorem constantCoeff_Acf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) = 1 := by
  simp [Acf, rt_constantCoeff_lam]

theorem rt_Acf_ne (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) ≠ 0 := by
  rw [constantCoeff_Acf]
  exact one_ne_zero

theorem rt_order_BA (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    2 ≤ (Bcf W wq * (Acf W wq)⁻¹).order := by
  exact rt_two_le_mul_right _ _ (rt_order_Bcf W wq)

theorem constantCoeff_thirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Z3 W wq) = 0 := by
  simp [Z3, rt_constantCoeff_lam_lemma (rt_order_Bcf W wq)]

theorem vieta1 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Acf W wq * (Xv 0 + Xv 1 + Z3 W wq) = -Bcf W wq := by
  have hA : Acf W wq * (Acf W wq)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (rt_Acf_ne W wq)
  unfold Z3
  linear_combination (-(Bcf W wq)) * hA

theorem var_zero_sub_var_one_ne_zero : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [MvPowerSeries.coeff_X, hs] at h1

private theorem chordCubic_var_zero_lemma (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (u : MvPowerSeries (Fin 2) ℂ_[p]) :
    G W u (lam wq * u + nu wq) = Acf W wq * u ^ 3 + Bcf W wq * u ^ 2 + Ccf W wq * u + Dcf W wq := by
  unfold G Acf Bcf Ccf Dcf
  ring

theorem chordCubic_var_zero {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Acf W wq * Xv 0 ^ 3 + Bcf W wq * Xv 0 ^ 2 + Ccf W wq * Xv 0 + Dcf W wq = 0 := by
  have hw : wv wq 0 = lam wq * Xv 0 + nu wq := by
    unfold nu
    ring
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 0

theorem chordCubic_var_one {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Acf W wq * Xv 1 ^ 3 + Bcf W wq * Xv 1 ^ 2 + Ccf W wq * Xv 1 + Dcf W wq = 0 := by
  have hw : wv wq 1 = lam wq * Xv 1 + nu wq := by
    unfold nu
    linear_combination (-1 : MvPowerSeries (Fin 2) ℂ_[p]) * lam_mul wq
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 1

theorem vieta2 {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Ccf W wq = Acf W wq * (Xv 0 * Xv 1 + Xv 0 * Z3 W wq + Xv 1 * Z3 W wq) := by
  have hK : Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq = 0 := by
    have hprod : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) *
        (Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq) = 0 := by
      linear_combination chordCubic_var_zero h - chordCubic_var_one h
    exact (mul_eq_zero.1 hprod).resolve_left var_zero_sub_var_one_ne_zero
  linear_combination hK - (Xv 0 + Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta1 W wq

theorem vieta3 {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Dcf W wq = -(Acf W wq * Xv 0 * Xv 1 * Z3 W wq) := by
  linear_combination chordCubic_var_zero h - (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * vieta1 W wq -
    (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta2 h

theorem zwEquation_thirdRoot {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (Z3 W wq) (lam wq * Z3 W wq + nu wq) = 0 := by
  rw [chordCubic_var_zero_lemma]
  linear_combination Z3 W wq ^ 2 * vieta1 W wq + Z3 W wq * vieta2 h + vieta3 h

theorem rt_G_map {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (G W u v) = G W (φ u) (φ v) := by
  simp only [G, map_add (f := _), map_sub, map_mul, map_pow, AlgHom.commutes]

theorem subst_thirdRoot_wSeries {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Z3 W wq) (wser wq) = lam wq * Z3 W wq + nu wq := by
  obtain ⟨z, hz⟩ : ∃ z, z = Z3 W wq := ⟨_, rfl⟩
  have hGv := zwEquation_thirdRoot h
  rw [← hz] at hGv ⊢
  have hz0 : MvPowerSeries.constantCoeff z = 0 := by rw [hz]; exact constantCoeff_thirdRoot W wq
  have ha : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero hz0
  obtain ⟨w, hw⟩ : ∃ w, w = PowerSeries.subst z (wser wq) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lam wq * z + nu wq := ⟨_, rfl⟩
  rw [← hw, ← hv]
  rw [← hv] at hGv
  have hGw : G W z w = 0 := by
    have h0 := congrArg (PowerSeries.substAlgHom ha) (G_wser h)
    rw [rt_G_map, map_zero, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha, ← hw] at h0
    exact h0
  have hw' : w = z ^ 3 * PowerSeries.subst z wq := by
    rw [hw, wser, ← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha]
  have hw0 : MvPowerSeries.constantCoeff w = 0 := by
    rw [hw', map_mul, map_pow, hz0]
    simp
  have hv0 : MvPowerSeries.constantCoeff v = 0 := by
    simp [hv, hz0, rt_constantCoeff_lam, rt_constantCoeff_nu]
  have hfac : G W z v - G W z w = (v - w) *
      (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) := by
    unfold G
    ring
  have hF : (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) ≠ 0 := by
    intro h0
    have h1 := congrArg MvPowerSeries.constantCoeff h0
    simp [hz0, hv0, hw0] at h1
  rw [hGv, hGw, sub_zero] at hfac
  exact (sub_eq_zero.1 ((mul_eq_zero.1 hfac.symm).resolve_right hF)).symm

theorem rt_coeff_BA (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (Bcf W wq * (Acf W wq)⁻¹) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (rt_order_BA W wq)
  norm_num [Finsupp.degree_single]

theorem thirdRoot_sub_var_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 0 ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h0
  simp [Z3, rt_coeff_BA, MvPowerSeries.coeff_X, hs, hs.symm] at h1

theorem thirdRoot_sub_var_one_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 1 ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [Z3, rt_coeff_BA, MvPowerSeries.coeff_X, hs, hs.symm] at h1

theorem thirdRoot_mem_coeffSubring {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    Z3 W wq ∈ SerS S (Fin 2) := by
  have hwq := wq_mem h1 h2 h3 h4 h6 h
  have hcc : ∀ a ∈ S, cc a ∈ SerS S (Fin 2) := fun a ha => (mem_SerS S _).2 fun e => by
    simp only [cc, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.coeff_C]
    split_ifs
    · exact ha
    · exact S.zero_mem
  have hX : ∀ i, (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := fun i =>
    (mem_SerS S _).2 fun e => by
      rw [MvPowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
  have hl : lam wq ∈ SerS S (Fin 2) := (mem_SerS S _).2 (lam_mem hwq)
  have hw0 : wv wq 0 ∈ SerS S (Fin 2) := (mem_SerS S _).2 fun e => by
    rw [coeff_wSeriesVar_zero]
    split_ifs
    · exact lamA_wser_mem hwq _
    · exact S.zero_mem
  have hn : nu wq ∈ SerS S (Fin 2) := sub_mem hw0 (mul_mem hl (hX 0))
  have h2' : (2 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (2 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 from one_add_one_eq_two.symm]
    exact add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem
  have h3' : (3 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (3 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 + 1 by ring]
    exact add_mem (add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem) (SerS S (Fin 2)).one_mem
  have hA : Acf W wq ∈ SerS S (Fin 2) := by
    unfold Acf
    exact add_mem (add_mem (add_mem (SerS S (Fin 2)).one_mem (mul_mem (hcc _ h2) hl)) (mul_mem (hcc _ h4) (pow_mem hl 2)))
      (mul_mem (hcc _ h6) (pow_mem hl 3))
  have hB : Bcf W wq ∈ SerS S (Fin 2) := by
    unfold Bcf
    exact add_mem (add_mem (add_mem (add_mem (mul_mem (hcc _ h1) hl) (mul_mem (hcc _ h2) hn))
      (mul_mem (hcc _ h3) (pow_mem hl 2))) (mul_mem (mul_mem (mul_mem h2' (hcc _ h4)) hl) hn))
      (mul_mem (mul_mem (mul_mem h3' (hcc _ h6)) (pow_mem hl 2)) hn)
  unfold Z3
  exact sub_mem (sub_mem (neg_mem (hX 0)) (hX 1)) (mul_mem hB (inv_mem_SerS S (constantCoeff_Acf W wq) hA))

end PI.AddIntG.Wk
end
end

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem Gv_algHom {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (Gv W u v) = Gv W (φ u) (φ v) := by
  simp [Gv, map_add (f := _), map_mul, map_sub, map_pow, AlgHom.commutes, map_ofNat]

theorem omega_at {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0) :
    PowerSeries.subst r (omegaW W wq) * Gv W r (PowerSeries.subst r (wser wq)) = -1 := by
  have hs : PowerSeries.HasSubst r := PowerSeries.HasSubst.of_constantCoeff_zero hr
  have key := congrArg (PowerSeries.substAlgHom hs) (omega_mul_Gv h)
  rw [map_mul, Gv_algHom, map_neg, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hs] at key
  exact key

theorem root_rel {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (j : Fin 2)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0)
    (hw : PowerSeries.subst r (wser wq) = lam wq * r + nu wq)
    (hG : G W r (lam wq * r + nu wq) = 0) :
    PowerSeries.subst r (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j r *
      (3 * Acf W wq * r ^ 2 + 2 * Bcf W wq * r + Ccf W wq) =
      r * MvPowerSeries.pderiv (R := ℂ_[p]) j (lam wq) + MvPowerSeries.pderiv (R := ℂ_[p]) j (nu wq) := by
  set D := MvPowerSeries.pderiv (R := ℂ_[p]) j with hDdef
  have hω := omega_at h hr
  rw [hw] at hω
  have hD := congrArg D hG
  rw [map_zero] at hD
  simp only [G, map_add (f := _), map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, nsmul_eq_mul, smul_zero, zero_smul, mul_zero, zero_mul,
    add_zero, zero_add, Nat.cast_ofNat] at hD
  simp only [Gv] at hω
  simp only [Acf, Bcf, Ccf, cc]
  linear_combination (PowerSeries.subst r (omegaW W wq)) * hD -
    (r * D (lam wq) + D (nu wq)) * hω

theorem var_zero_sub_var_one_ne : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
  intro h
  have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro hs
    have h3 := congrArg (fun f => f 0) hs
    simp at h3
  simp [Xv, MvPowerSeries.coeff_X, hne] at h2

theorem abel_cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  unfold flog
  simp

theorem abel {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Z3 W wq) (flog W wq) = 0 := by
  classical
  have hc0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [Xv]
  have hc1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [Xv]
  have hc2 := constantCoeff_thirdRoot W wq
  have hw0 : PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq) = lam wq * Xv 0 + nu wq := by
    show wv wq 0 = _
    simp only [nu]
    ring
  have hw1 : PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq) = lam wq * Xv 1 + nu wq :=
    wv_line1 wq
  have hw2 := subst_thirdRoot_wSeries h
  have hG0 : G W (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (lam wq * Xv 0 + nu wq) = 0 := by
    rw [← hw0]
    exact G_wv h 0
  have hG1 : G W (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (lam wq * Xv 1 + nu wq) = 0 := by
    rw [← hw1]
    exact G_wv h 1
  have hG2 := zwEquation_thirdRoot h
  have hsub : ∀ r : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff r = 0 → ∀ j,
      MvPowerSeries.pderiv (R := ℂ_[p]) j (PowerSeries.subst r (flog W wq)) =
        PowerSeries.subst r (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j r := by
    intro r hr j
    rw [pderiv_subst (PowerSeries.HasSubst.of_constantCoeff_zero hr), derivative_flog]
  have hA : Acf W wq ≠ 0 := fun h0 => by
    have h3 := constantCoeff_Acf W wq
    rw [h0, map_zero] at h3
    exact zero_ne_one h3
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro hs
    have h4 := congrArg (fun f => f 0) hs
    simp at h4
  have h01 : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := var_zero_sub_var_one_ne
  have h02 : (Xv 0 - Z3 W wq : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have h3 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
    have hBA := rt_coeff_BA W wq 0
    simp [Z3, Xv, MvPowerSeries.coeff_X, hne, hBA] at h3 <;> norm_num at h3
  have h12 : (Xv 1 - Z3 W wq : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have h3 := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h0
    have hBA := rt_coeff_BA W wq 1
    simp [Z3, Xv, MvPowerSeries.coeff_X, hne.symm, hBA] at h3 <;> norm_num at h3
  have key : ∀ j, PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) +
      PowerSeries.subst (Z3 W wq) (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j (Z3 W wq) = 0 := by
    intro j
    have e0 := root_rel h j hc0 hw0 hG0
    have e1 := root_rel h j hc1 hw1 hG1
    have e2 := root_rel h j hc2 hw2 hG2
    have v1 := vieta1 W wq
    have v2 := vieta2 h
    set T0 := PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) with hT0
    set T1 := PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (omegaW W wq) *
        MvPowerSeries.pderiv (R := ℂ_[p]) j (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) with hT1
    set T2 := PowerSeries.subst (Z3 W wq) (omegaW W wq) * MvPowerSeries.pderiv (R := ℂ_[p]) j (Z3 W wq) with hT2
    have hprod : (T0 + T1 + T2) * (Acf W wq * ((Xv 0 - Xv 1) * (Xv 0 - Z3 W wq) * (Xv 1 - Z3 W wq))) = 0 := by
      linear_combination (Xv 1 - Z3 W wq) * e0 - (Xv 0 - Z3 W wq) * e1 + (Xv 0 - Xv 1) * e2 -
        ((Xv 1 - Z3 W wq) * T0 * 2 * Xv 0 - (Xv 0 - Z3 W wq) * T1 * 2 * Xv 1 +
          (Xv 0 - Xv 1) * T2 * 2 * Z3 W wq) * v1 -
        ((Xv 1 - Z3 W wq) * T0 - (Xv 0 - Z3 W wq) * T1 + (Xv 0 - Xv 1) * T2) * v2
    rcases mul_eq_zero.1 hprod with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero hA (mul_ne_zero (mul_ne_zero h01 h02) h12))
  set F := PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Z3 W wq) (flog W wq) with hFdef
  have hF : ∀ j, MvPowerSeries.pderiv (R := ℂ_[p]) j F = 0 := fun j => by
    rw [hFdef, map_add (f := _), map_add (f := _), hsub _ hc0, hsub _ hc1, hsub _ hc2]
    exact key j
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (abel_cc_flog W wq)
  have hcc : ∀ r : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff r = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst r (flog W wq)) = 0 := by
    intro r hr
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero hr
    have hm := map_mul (PowerSeries.substAlgHom hs) PowerSeries.X g
    rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, ← hg] at hm
    rw [hm, map_mul, hr, zero_mul]
  ext e
  rw [map_zero]
  by_cases he : e = 0
  · subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hFdef, map_add (f := _), map_add (f := _), hcc _ hc0, hcc _ hc1,
      hcc _ hc2, add_zero, add_zero]
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 he
    have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have he' : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
    have h3 := MvPowerSeries.coeff_pderiv (i := i) F (e - Finsupp.single i 1)
    rw [hF i, map_zero, he'] at h3
    have h4 : (((e - Finsupp.single i 1 : Fin 2 →₀ ℕ) i : ℕ) : ℂ_[p]) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    exact (mul_eq_zero.1 h3.symm).resolve_right h4

end PI.AddIntG.Wk
end
end

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p] :=
  fun i => if i = 0 then 0 else Z3 W wq

theorem bZ_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    ∀ i, MvPowerSeries.constantCoeff (bZ W wq i) = 0 := by
  intro i
  unfold bZ
  split_ifs
  · exact map_zero _
  · exact constantCoeff_thirdRoot W wq

theorem hasSubst_bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.HasSubst (bZ W wq) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (bZ_const W wq)

theorem Fch_eq (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Fch W wq = MvPowerSeries.subst (bZ W wq) (Z3 W wq) := rfl

theorem subst_psubst {a : MvPowerSeries (Fin 2) ℂ_[p]} (ha : PowerSeries.HasSubst a)
    {b : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hb]

theorem constantCoeff_flog' (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold PI.AddIntG.flog
  rw [PowerSeries.coeff_mk, if_pos rfl]

theorem constantCoeff_Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Fch W wq) = 0 := by
  rw [Fch_eq]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_bZ W wq) (bZ_const W wq) (constantCoeff_thirdRoot W wq)

theorem Fch_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, MvPowerSeries.coeff n (Fch W wq) ∈ S := by
  have hZ := thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h
  have hb : ∀ i, bZ W wq i ∈ SerS S (Fin 2) := by
    intro i
    unfold bZ
    split_ifs
    · exact zero_mem _
    · exact hZ
  rw [Fch_eq]
  exact (mem_SerS S _).mp (mvsubst_mem_SerS S (bZ_const W wq) hb hZ)

theorem flog_Fch {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Fch W wq) (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) := by
  have hA := abel h
  have hb := hasSubst_bZ W wq
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hZ : PowerSeries.HasSubst (Z3 W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_thirdRoot W wq)
  have hB := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) hb) hA
  rw [map_add (f := _), map_add (f := _), map_zero, MvPowerSeries.coe_substAlgHom, subst_psubst (hX 0) hb,
    subst_psubst (hX 1) hb, subst_psubst hZ hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    ← Fch_eq] at hB
  have h0 : bZ W wq 0 = 0 := by simp [bZ]
  have h1' : bZ W wq 1 = Z3 W wq := by simp [bZ]
  rw [h0, h1', PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_flog' W wq)] at hB
  linear_combination hB - hA

theorem formalGroupLawExists : KeyF := by
  intro p _ S W wq h1 h2 h3 h4 h6 h
  exact ⟨Fch W wq, Fch_mem h1 h2 h3 h4 h6 h, constantCoeff_Fch W wq, flog_Fch h⟩

end PI.AddIntG.Wk
