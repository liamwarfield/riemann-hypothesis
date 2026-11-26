module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviFinsetSum

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoefNonneg
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.TelePoint
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviLogfk
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 b : Frame X.Ψ r} {z u : V (nd X)}

def Ck (X : Data E r) (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  ∑ a : Fin k, (Dsg X (Fin.castLE (Nat.le_of_lt_succ k.isLt) a))⁻¹ *
    Sa (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) a

theorem fk_zero (τ : X.Ψ) (k : Fin (r + 1)) : fk X b z u τ k 0 ≠ 0 := by
  unfold fk
  rw [fY_zero]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  simp only [Dsg, sgn]
  split_ifs <;> norm_num

theorem cd_logfk (τ : X.Ψ) (k : Fin (r + 1)) :
    ContDiffAt ℝ 2 (fun v => Real.log |fk X b z u τ k v|) 0 := by
  have h0 : fk X b z u τ k 0 ≠ 0 := fk_zero τ k
  have hc : ContDiff ℝ 2 (fk X b z u τ k) := by
    unfold fk fY Gz
    simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [← starRingEnd_apply, ← Complex.conjCLE_apply, ← Complex.reCLM_apply]
    fun_prop
  have hl : ContDiffAt ℝ 2 Real.log (fk X b z u τ k 0) := Real.contDiffAt_log.mpr h0
  simp only [Real.log_abs]
  exact hl.comp 0 hc.contDiffAt

theorem levi_logfk (τ : X.Ψ) (k : Fin (r + 1)) :
    levi (fun v => Real.log |fk X b z u τ k v|) 0 (fun _ => 1) = Ck X b z u τ k :=
  core_levi (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (Dsg_ne X)

theorem line_levi (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (la : Wt X.Ψ r) :
    levi (fun v : Fin 1 → ℂ => -2 * Real.log (X.nfac la (cpt X x0 (z + lineL u v)))) 0 (fun _ => 1) =
      ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) := by
  have hcont : ∀ τ k, ContinuousAt (fk X b z u τ k) 0 := fun τ k =>
    (contDiff_fY _ _ _).continuous.continuousAt
  have hev : ∀ᶠ v in 𝓝 (0 : Fin 1 → ℂ), ∀ τ k, fk X b z u τ k v ≠ 0 := by
    rw [Filter.eventually_all]
    intro τ
    rw [Filter.eventually_all]
    intro k
    exact (hcont τ k).eventually_ne (fk_zero τ k)
  have hBne : ∀ τ (k : Fin (r + 1)), ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
      (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 ≠ 0 := fun τ k =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (det_lead_ne _ (upper_inv _ (hb τ).1 (fun a c h => (hb τ).2 a c h))
      (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hb τ).1) _))
  have hterm : ∀ τ (i : Fin r), (fun v => (la τ i : ℝ) * ((cB X b τ i.succ + Real.log |fk X b z u τ i.succ v|) -
      (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|))) =
      fun v => ((la τ i : ℝ) * (cB X b τ i.succ - cB X b τ i.castSucc) +
        (la τ i : ℝ) * Real.log |fk X b z u τ i.succ v|) + (-(la τ i : ℝ)) * Real.log |fk X b z u τ i.castSucc v| := by
    intro τ i; funext v; ring
  have hcdt : ∀ τ (i : Fin r), ContDiffAt ℝ 2 (fun v => (la τ i : ℝ) * ((cB X b τ i.succ +
      Real.log |fk X b z u τ i.succ v|) - (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|))) 0 := by
    intro τ i
    rw [hterm]
    exact (contDiffAt_const.add (contDiffAt_const.mul (cd_logfk τ _))).add
      (contDiffAt_const.mul (cd_logfk τ _))
  have hEq : (fun v : Fin 1 → ℂ => -2 * Real.log (X.nfac la (cpt X x0 (z + lineL u v)))) =ᶠ[𝓝 0]
      fun v => ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * ((cB X b τ i.succ + Real.log |fk X b z u τ i.succ v|) -
        (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|)) := by
    filter_upwards [hev] with v hv
    have hd : ∀ τ k, dmin X.Gm (cpt X x0 (z + lineL u v)) τ k ≠ 0 := fun τ k => by
      rw [lineL_apply]
      intro h0
      have h1 := dmin_line_norm (u := u) hb hgram v τ k
      rw [h0, norm_zero] at h1
      exact mul_ne_zero (hBne τ k) (abs_ne_zero.2 (hv τ k)) h1.symm
    rw [neg2log_nfac X la _ hd]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [lineL_apply, dmin_line_norm (u := u) hb hgram v τ _, dmin_line_norm (u := u) hb hgram v τ _,
      Real.log_mul (hBne _ _) (abs_ne_zero.2 (hv _ _)), Real.log_mul (hBne _ _) (abs_ne_zero.2 (hv _ _))]
    rfl
  rw [levi_congr hEq, levi_finset_sum _ _ _ _ (fun τ _ => ContDiffAt.sum fun i _ => hcdt τ i)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [levi_finset_sum _ _ _ _ (fun i _ => hcdt τ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm, levi_add_smul _ (contDiffAt_const.add (contDiffAt_const.mul (cd_logfk τ _))) (cd_logfk τ _),
    levi_affine _ _ _ _ _ (cd_logfk τ _), levi_logfk, levi_logfk]
  ring

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Ck_eq (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) :
    Ck X b z u τ k = ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < k ∧ (k : ℕ) ≤ j then
      (Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2) else 0 := by
  calc Ck X b z u τ k
      = ∑ a : Fin r, if (a : ℕ) < k then (Dsg X a)⁻¹ *
          ∑ j : Fin r, (if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0) else 0 :=
        sum_castLE' (Nat.le_of_lt_succ k.isLt) (fun a : Fin r => (Dsg X a)⁻¹ *
          ∑ j : Fin r, if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0)
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < k
      · rw [if_pos ha, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : (k : ℕ) ≤ (j : ℕ)
        · rw [if_pos hj, if_pos ⟨ha, hj⟩]
        · rw [if_neg hj, if_neg (fun h => hj h.2), mul_zero]
      · rw [if_neg ha, eq_comm]
        exact Finset.sum_eq_zero fun j _ => if_neg (fun h => ha h.1)

theorem tele_point (a j i : Fin r) :
    ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
      (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) =
      if (a : ℕ) < j then ((if i = a then 1 else 0) - (if i = j then 1 else 0)) else 0 := by
  simp only [Fin.ext_iff]
  split_ifs <;> (try norm_num) <;> omega

theorem tele_sum (la : Fin r → ℝ) (a j : Fin r) :
    ∑ i : Fin r, la i * ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
      (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) = if (a : ℕ) < j then la a - la j else 0 := by
  simp_rw [tele_point]
  split_ifs with h
  · simp [mul_sub, Finset.sum_sub_distrib]
  · simp

def coef (la : Wt X.Ψ r) (τ : X.Ψ) (a j : Fin r) : ℝ := Dsg X j / Dsg X a * ((la τ a : ℝ) - la τ j)

theorem tele (b : Frame X.Ψ r) (z u : V (nd X)) (la : Wt X.Ψ r) (τ : X.Ψ) :
    ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) =
      ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then coef X la τ a j * ‖Yd X b z u τ j a‖ ^ 2 else 0 := by
  have hdiff : ∀ i : Fin r, Ck X b z u τ i.succ - Ck X b z u τ i.castSucc =
      ∑ a : Fin r, ∑ j : Fin r, ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)) := by
    intro i
    rw [Ck_eq, Ck_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> ring
  calc ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc)
      = ∑ i : Fin r, ∑ a : Fin r, ∑ j : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiff i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin r, ∑ j : Fin r, ∑ i : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
      have hts := tele_sum (fun i => (la τ i : ℝ)) a j
      beta_reduce at hts
      rw [show (∑ i : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
            (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)))) =
          (∑ i : Fin r, (la τ i : ℝ) * ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
            (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0))) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring, hts]
      by_cases haj : (a : ℕ) < j
      · rw [if_pos haj, if_pos haj, coef, div_eq_mul_inv]
        ring
      · rw [if_neg haj, if_neg haj, zero_mul]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem coef_nonneg (la : Wt X.Ψ r) (hdom : X.IsDominant la) (τ : X.Ψ) (a j : Fin r) (h : (a : ℕ) < j) :
    0 ≤ coef X la τ a j := by
  obtain ⟨h1, h2', h3⟩ := hdom τ
  have haj : a < j := Fin.lt_def.2 h
  unfold coef Dsg sgn
  by_cases hj : (j : ℕ) < X.p0
  · have ha : (a : ℕ) < X.p0 := by omega
    have hz := h1 a j haj.le hj
    have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
    rw [if_pos hj, if_pos ha]
    norm_num
    linarith
  · by_cases ha : (a : ℕ) < X.p0
    · have hz := h3 a j ha (by omega)
      have hr : (la τ a : ℝ) ≤ la τ j := by exact_mod_cast hz
      rw [if_neg hj, if_pos ha]
      norm_num
      linarith
    · have hz := h2' a j (by omega) haj.le
      have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
      rw [if_neg hj, if_neg ha]
      norm_num
      linarith

theorem coef_pos (la : Wt X.Ψ r) (hs : IsStrictDom X la) (τ : X.Ψ) (a j : Fin r) (h : (a : ℕ) < j) :
    0 < coef X la τ a j := by
  obtain ⟨h1, h2', h3⟩ := hs τ
  have haj : a < j := Fin.lt_def.2 h
  unfold coef Dsg sgn
  by_cases hj : (j : ℕ) < X.p0
  · have ha : (a : ℕ) < X.p0 := by omega
    have hz := h1 a j haj hj
    have hr : (la τ j : ℝ) < la τ a := by exact_mod_cast hz
    rw [if_pos hj, if_pos ha]
    norm_num
    linarith
  · by_cases ha : (a : ℕ) < X.p0
    · have hz := h3 a j ha (by omega)
      have hr : (la τ a : ℝ) < la τ j := by exact_mod_cast hz
      rw [if_neg hj, if_pos ha]
      norm_num
      linarith
    · have hz := h2' a j (by omega) haj
      have hr : (la τ j : ℝ) < la τ a := by exact_mod_cast hz
      rw [if_neg hj, if_neg ha]
      norm_num
      linarith

theorem Lin_ne (u : V (nd X)) (hu : u ≠ 0) : ∃ τ, KapPf.Lin X τ u ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hu
  ext i
  rcases he : (Fintype.equivFin (Ent X)).symm i with ⟨τ, ⟨⟨x, c⟩, hxc⟩⟩
  have hi : Fintype.equivFin (Ent X) ⟨τ, ⟨(x, c), hxc⟩⟩ = i := by
    rw [← he]
    exact Equiv.apply_symm_apply _ _
  have h0 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M x c) (hall τ)
  simp only [KapPf.Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, KapPf.embF,
    KapPf.vecOf, hxc, dite_true, Matrix.zero_apply] at h0
  rw [hi] at h0
  simpa using h0

theorem Xd_lower (z u : V (nd X)) (τ : X.Ψ) (i j : Fin r) (hij : i ≤ j) : Xd X z u τ i j = 0 := by
  have hL : (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.1 hab
    simp [mat, nmat, not_lt.2 hab'.le, hab'.ne]
  have : Invertible (mat (nmat X z) τ) :=
    (mat (nmat X z) τ).invertibleOfIsUnitDet (nmat_det_unit X z τ)
  have hLi := Matrix.blockTriangular_inv_of_blockTriangular hL
  unfold Xd
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hLi (OrderDual.toDual_lt_toDual.2 hik), zero_mul]
  · have hkj : ¬ j < k := fun h => hik (lt_of_le_of_lt hij h)
    have hz : KapPf.Lin X τ u k j = 0 := by
      simp [KapPf.Lin, KapPf.embF, hkj]
    rw [hz, mul_zero]

theorem Yd_ne (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (hu : u ≠ 0) :
    ∃ τ, ∃ a j : Fin r, (a : ℕ) < j ∧ Yd X b z u τ j a ≠ 0 := by
  obtain ⟨τ, hτ⟩ := Lin_ne X u hu
  refine ⟨τ, ?_⟩
  by_contra hall
  push Not at hall
  apply hτ
  have hN : IsUnit (mat (nmat X z) τ).det := nmat_det_unit X z τ
  have hB : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hBd : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have : Invertible (mat b τ) := (mat b τ).invertibleOfIsUnitDet hBd
  have hY : (Yd X b z u τ).BlockTriangular id := fun a c hca => hall c a hca
  have hX : Xd X z u τ = mat b τ * Yd X b z u τ * (mat b τ)⁻¹ := by
    unfold Yd
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hBd]
  have hXu : (Xd X z u τ).BlockTriangular id := by
    rw [hX]
    exact (hB.mul hY).mul (Matrix.blockTriangular_inv_of_blockTriangular hB)
  have hXd : Xd X z u τ = 0 := by
    ext i j
    rcases lt_or_ge j i with h | h
    · exact hXu h
    · exact Xd_lower X z u τ i j h
  have hLin : KapPf.Lin X τ u = mat (nmat X z) τ * Xd X z u τ := by
    unfold Xd
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hN]
  rw [hLin, hXd, Matrix.mul_zero]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_coord (j : Fin (nd X)) : ContDiff ℝ 2 fun w : V (nd X) => w j := by
  first
  | fun_prop
  | exact ((EuclideanSpace.proj j).restrictScalars ℝ).contDiff
  | exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (nd X) => ℂ) j).contDiff

theorem cd_nmat (τ : X.Ψ) (a c : Fin r) : ContDiff ℝ 2 fun w : V (nd X) => mat (nmat X w) τ a c := by
  simp only [mat, nmat, Matrix.of_apply]
  split_ifs
  · exact cd_coord X _
  · exact contDiff_const
  · exact contDiff_const

theorem cd_dmin (x0 : Frame X.Ψ r) (τ : X.Ψ) (k : Fin (r + 1)) :
    ContDiff ℝ 2 fun w : V (nd X) => dmin X.Gm (cpt X x0 w) τ k := by
  have hM : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) => (mat x0 τ * mat (nmat X w) τ) a c :=
    cd_mul (fun _ => mat x0 τ) (fun w => mat (nmat X w) τ) (fun _ _ => contDiff_const) (cd_nmat X τ)
  have hMt : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) => ((mat x0 τ * mat (nmat X w) τ)ᵀ) a c :=
    fun a c => hM c a
  have hMc : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) =>
      ((mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)) a c :=
    fun a c => Complex.conjCLE.contDiff.comp (hM a c)
  have hG : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) =>
      ((mat x0 τ * mat (nmat X w) τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)) a c :=
    cd_mul _ _ (cd_mul _ _ hMt (fun _ _ => contDiff_const)) hMc
  unfold dmin lminor
  simp only [FrameDegreeData.gram_eq]
  exact cd_det (fun w : V (nd X) => ((mat x0 τ * mat (nmat X w) τ)ᵀ * X.Gm.map τ.1 *
    (mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix _ _) (fun a c => hG _ _)

theorem cd_lognorm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (d : F → ℂ) (hd : ContDiff ℝ 2 d)
    (z : F) (hz : d z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log ‖d w‖) z := by
  have h1 : ContDiffAt ℝ 2 (fun w => ‖d w‖) z := (hd.contDiffAt).norm ℝ hz
  exact h1.log (norm_ne_zero_iff.mpr hz)

theorem cd_h (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) (la : Wt X.Ψ r) :
    ContDiffAt ℝ 2 (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z := by
  have hne : ∀ τ k, dmin X.Gm (cpt X x0 z) τ k ≠ 0 := fun τ k h => by
    have := (hz τ).2 k
    rw [h] at this
    simp at this
  have hev : ∀ᶠ w in 𝓝 z, ∀ τ k, dmin X.Gm (cpt X x0 w) τ k ≠ 0 := by
    rw [Filter.eventually_all]; intro τ
    rw [Filter.eventually_all]; intro k
    exact (cd_dmin X x0 τ k).continuous.continuousAt.eventually_ne (hne τ k)
  have hEq : (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) =ᶠ[𝓝 z] fun w => ∑ τ, ∑ i : Fin r,
      (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x0 w) τ i.succ‖ -
        Real.log ‖dmin X.Gm (cpt X x0 w) τ i.castSucc‖) := by
    filter_upwards [hev] with w hw
    exact neg2log_nfac X la _ hw
  refine ContDiffAt.congr_of_eventuallyEq ?_ hEq
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul
    ((cd_lognorm _ (cd_dmin X x0 τ _) z (hne τ _)).sub (cd_lognorm _ (cd_dmin X x0 τ _) z (hne τ _)))

theorem levi_formula (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X la τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
  rw [leviV_re_line (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z (cd_h X x0 z hz la) ξ,
    line_levi hb hgram la]
  exact Finset.sum_congr rfl fun τ _ => tele X b z _ la τ

theorem curvature_statement_holds : CurvGGStatement (E := E) := by
  intro r X la x0 z hz
  obtain ⟨b, hb, hgr⟩ := MajorantNormalForms.exists_normal_frame X hz
  have hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ => (hgr τ).1
  have hval : ∀ ξ : Fin (nd X) → ℂ,
      (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
        ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
          coef X la τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
    intro ξ
    rw [leviV_re_line (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z (cd_h X x0 z hz la) ξ,
      line_levi hb hgram la]
    exact Finset.sum_congr rfl fun τ _ => tele X b z _ la τ
  constructor
  · intro hdom ξ
    rw [hval]
    refine Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact mul_nonneg (coef_nonneg X la hdom τ a j h) (sq_nonneg _)
    · exact le_rfl
  · intro hs ξ hξ
    rw [hval]
    have hu : (WithLp.toLp 2 ξ : V (nd X)) ≠ 0 := fun h => hξ (by simpa using congrArg WithLp.ofLp h)
    obtain ⟨τ, a, j, haj, hY⟩ := Yd_ne X b hb z _ hu
    have hnn : ∀ τ' (a' j' : Fin r), 0 ≤ (if (a' : ℕ) < j' then
        coef X la τ' a' j' * ‖Yd X b z (WithLp.toLp 2 ξ) τ' j' a'‖ ^ 2 else 0) := by
      intro τ' a' j'
      split_ifs with h
      · exact mul_nonneg (coef_pos X la hs τ' a' j' h).le (sq_nonneg _)
      · exact le_rfl
    refine Finset.sum_pos' (fun τ' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun j' _ => hnn τ' a' j')
      ⟨τ, Finset.mem_univ _, Finset.sum_pos' (fun a' _ => Finset.sum_nonneg fun j' _ => hnn τ a' j')
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun j' _ => hnn τ a j') ⟨j, Finset.mem_univ _, ?_⟩⟩⟩
    rw [if_pos haj]
    exact mul_pos (coef_pos X la hs τ a j haj) (pow_pos (norm_pos_iff.2 hY) 2)

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
