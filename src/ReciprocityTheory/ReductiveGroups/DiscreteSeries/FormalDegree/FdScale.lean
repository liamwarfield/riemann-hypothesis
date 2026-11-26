module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem finrank_pcoord (ε : Fin n → Bool) :
    Module.finrank ℝ (PCoord ε → ℂ) = 2 * (pOf ε * qOf ε) := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_PCoord, smul_eq_mul, mul_comm]

theorem lintegral_pcoord_smul {ε : Fin n → Bool} (f : (PCoord ε → ℂ) → ENNReal) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, f z = ENNReal.ofReal (s ^ (2 * (pOf ε * qOf ε))) * ∫⁻ y, f ((s : ℂ) • y) := by
  have hsm : (fun y : PCoord ε → ℂ => f ((s : ℂ) • y)) = fun y => f (s • y) := by
    funext y
    rw [Complex.coe_smul]
  have key : ∫⁻ y, f (s • y) =
      ENNReal.ofReal |(s ^ Module.finrank ℝ (PCoord ε → ℂ))⁻¹| * ∫⁻ z, f z := by
    have h1 := lintegral_map_equiv f (MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')
      (μ := volume)
    have h2 : (⇑(MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')) = (s • ·) := rfl
    rw [h2, Measure.map_addHaar_smul volume hs.ne', lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  rw [hsm, key, finrank_pcoord, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => (toMK k * pmat z * (toMK k)ᴴ) ab.1.1 ab.1.2

theorem adKAux_K_facts {ε : Fin n → Bool} (k : KG ε) :
    (toMK k)ᴴ * toMK k = 1 ∧ toMK k * Jm ε = Jm ε * toMK k ∧ (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
  obtain ⟨hu, hc⟩ := k.2
  have h1 : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have h2 : toMK k * (toMK k)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have hc' : toMK k * Jm ε = Jm ε * toMK k := by
    first
      | exact hc
      | exact hc.symm
  refine ⟨h1, hc', ?_⟩
  calc (toMK k)ᴴ * Jm ε = (toMK k)ᴴ * Jm ε * (toMK k * (toMK k)ᴴ) := by rw [h2, Matrix.mul_one]
    _ = (toMK k)ᴴ * (Jm ε * toMK k) * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
    _ = (toMK k)ᴴ * (toMK k * Jm ε) * (toMK k)ᴴ := by rw [hc']
    _ = (toMK k)ᴴ * toMK k * Jm ε * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (toMK k)ᴴ := by rw [h1, Matrix.one_mul]

theorem inP_conj₂ {ε : Fin n → Bool} (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) :
    inP ε (toMK k * X * (toMK k)ᴴ) := by
  obtain ⟨h1, h2, h3⟩ := adKAux_K_facts k
  obtain ⟨hG, hP⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc toMK k * (Xᴴ * (toMK k)ᴴ) * Jm ε + Jm ε * (toMK k * X * (toMK k)ᴴ)
        = toMK k * Xᴴ * ((toMK k)ᴴ * Jm ε) + (Jm ε * toMK k) * X * (toMK k)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * Xᴴ * (Jm ε * (toMK k)ᴴ) + (toMK k * Jm ε) * X * (toMK k)ᴴ := by rw [h3, ← h2]
      _ = toMK k * (Xᴴ * Jm ε + Jm ε * X) * (toMK k)ᴴ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hG, Matrix.mul_zero, Matrix.zero_mul]
  · calc toMK k * X * (toMK k)ᴴ * Jm ε = toMK k * X * ((toMK k)ᴴ * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = toMK k * X * (Jm ε * (toMK k)ᴴ) := by rw [h3]
      _ = toMK k * (X * Jm ε) * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
      _ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hP]
      _ = -((toMK k * Jm ε) * X * (toMK k)ᴴ) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by rw [h2]; simp only [Matrix.mul_assoc]

theorem pmat_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    pmat (adK k z) = toMK k * pmat z * (toMK k)ᴴ := pmat_coords _ (inP_conj₂ k _ (pmat_inP z))

theorem adKAux_hs_eq (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (trace (M * Mᴴ)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    hs (pmat (adK k z)) = hs (pmat z) := by
  rw [pmat_adK, adKAux_hs_eq, adKAux_hs_eq]
  obtain ⟨h1, -, -⟩ := adKAux_K_facts k
  congr 1
  have e : toMK k * pmat z * (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ)ᴴ =
      toMK k * (pmat z * (pmat z)ᴴ) * (toMK k)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc toMK k * pmat z * (toMK k)ᴴ * (toMK k * ((pmat z)ᴴ * (toMK k)ᴴ))
        = toMK k * pmat z * ((toMK k)ᴴ * toMK k) * ((pmat z)ᴴ * (toMK k)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * (pmat z * (pmat z)ᴴ) * (toMK k)ᴴ := by
          rw [h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm (toMK k * (pmat z * (pmat z)ᴴ)) (toMK k)ᴴ, ← Matrix.mul_assoc, h1,
    Matrix.one_mul]

theorem adKAux_pev_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : pev (adK k z) = pev z := by
  obtain ⟨h1, -, -⟩ := adKAux_K_facts k
  unfold pev
  rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, pmat_adK, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem jac_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : Jac (adK k z) = Jac z := by
  unfold Jac
  rw [adKAux_pev_adK]

theorem adKAux_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases hu : u = 0
  · simp [hu]
  · rw [if_neg (neg_ne_zero.mpr hu), if_neg hu, Real.sinh_neg, neg_div_neg_eq]

theorem adKAux_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with hu
  · exact one_pos
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h
    · exact div_pos (Real.sinh_pos_iff.mpr h) h

def adjointCompactJacobianFactor (x : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (x a - x b)

theorem adKAuxJ_pos (x : Fin n → ℝ) : 0 < adjointCompactJacobianFactor x := by
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => adKAux_shc_pos _

theorem adKAuxJ_sq (x : Fin n → ℝ) : adjointCompactJacobianFactor x ^ 2 = ∏ a, ∏ b, shc (x a - x b) := by
  have hsym : ∀ a b, shc (x a - x b) = shc (x b - x a) := fun a b => by
    rw [← adKAux_shc_neg, neg_sub]
  have h1 : ∀ a : Fin n, ∏ b, shc (x a - x b) =
      (∏ b ∈ univ.filter (fun b => a < b), shc (x a - x b)) *
        ∏ b ∈ univ.filter (fun b => b < a), shc (x a - x b) := by
    intro a
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun b => a < b)]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter fun b => ¬ a < b) (fun b => b < a)]
    have e1 : (univ.filter fun b : Fin n => ¬ a < b).filter (fun b => b < a) =
        univ.filter (fun b => b < a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨not_lt.mpr h.le, h⟩
    have e2 : ∏ b ∈ (univ.filter fun b : Fin n => ¬ a < b).filter (fun b => ¬ b < a),
        shc (x a - x b) = 1 := by
      apply Finset.prod_eq_one
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hba : b = a := le_antisymm (not_lt.mp hb.1) (not_lt.mp hb.2)
      rw [hba, sub_self]
      simp [shc]
    rw [e1, e2, mul_one]
  have h2 : ∏ a, ∏ b ∈ univ.filter (fun b => b < a), shc (x a - x b) = adjointCompactJacobianFactor x := by
    rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a => b < a)) (by intro a b; simp)]
    unfold adjointCompactJacobianFactor
    exact Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun a _ => hsym a b
  rw [sq, Finset.prod_congr rfl fun a _ => h1 a, Finset.prod_mul_distrib, h2]
  rfl

theorem adKAux_prod_mset (x : Fin n → ℝ) : ∏ a, ∏ b, shc (x a - x b) =
    ((univ.val.map x).map fun u => ((univ.val.map x).map fun v => shc (u - v)).prod).prod := by
  simp only [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]

theorem adKAuxJ_mset (x y : Fin n → ℝ) (h : univ.val.map x = univ.val.map y) : adjointCompactJacobianFactor x = adjointCompactJacobianFactor y := by
  have h2 : adjointCompactJacobianFactor x ^ 2 = adjointCompactJacobianFactor y ^ 2 := by
    rw [adKAuxJ_sq, adKAuxJ_sq, adKAux_prod_mset, adKAux_prod_mset, h]
  exact (pow_left_inj₀ (adKAuxJ_pos x).le (adKAuxJ_pos y).le two_ne_zero).mp h2

theorem adKAux_pmat_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : pmat (-z) = -pmat z := by
  ext a b
  simp only [pmat, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem adKAux_pev_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    univ.val.map (pev (-z)) = univ.val.map (fun a => -pev z a) := by
  have hA := pmat_isHermitian z
  have hch : (pmat (-z)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (((-pev z i : ℝ)) : ℂ)) := by
    rw [adKAux_pmat_neg]
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_neg, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp [Matrix.charpoly_diagonal, pev, Matrix.diagonal_neg]
  have hr := (pmat_isHermitian (-z)).roots_charpoly_eq_eigenvalues
  rw [hch, Finset.prod_eq_multiset_prod] at hr
  rw [show (Multiset.map (fun i => Polynomial.X - Polynomial.C ((-pev z i : ℝ) : ℂ)) univ.val) =
      (univ.val.map (fun i => ((-pev z i : ℝ) : ℂ))).map (fun c => Polynomial.X - Polynomial.C c) by
      rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have := congrArg (Multiset.map Complex.re) hr
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
  exact this.symm

theorem jac_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jac (-z) = Jac z := by
  show adjointCompactJacobianFactor (pev (-z)) = adjointCompactJacobianFactor (pev z)
  rw [adKAuxJ_mset (pev (-z)) (fun a => -pev z a) (adKAux_pev_neg z)]
  unfold adjointCompactJacobianFactor
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [show -pev z a - -pev z b = -(pev z a - pev z b) by ring, adKAux_shc_neg]

theorem adKAux_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp [star_add]

theorem adKAux_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

def adjointCompactLinearAction {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, adKAux_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, adKAux_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply,
      Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem adKAux_norm_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    ∑ ab, ‖adK k z ab‖ ^ 2 = ∑ ab, ‖z ab‖ ^ 2 := by
  have h := hs_adK k z
  rw [hs_pmat, hs_pmat] at h
  linarith

theorem adK_measurePreserving {ε : Fin n → Bool} (k : KG ε) :
    MeasurePreserving (adK k) (volume : Measure (PCoord ε → ℂ)) volume := by
  set f := adjointCompactLinearAction k with hf
  have hq : ∀ z, ∑ ab, ‖f z ab‖ ^ 2 = ∑ ab, ‖z ab‖ ^ 2 := adKAux_norm_adK k
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h0 := hq z
    rw [hz] at h0
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at h0
    funext ab
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).mp h0.symm ab (mem_univ _)
    simpa using this
  have hdet : LinearMap.det f ≠ 0 :=
    (((LinearMap.isUnit_iff_ker_eq_bot f).mpr hinj).map LinearMap.det).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (PCoord ε → ℂ))) hdet
  have hcont : Continuous f := LinearMap.continuous_of_finiteDimensional f
  set S := {z : PCoord ε → ℂ | ∑ ab, ‖z ab‖ ^ 2 < 1} with hSdef
  have hSo : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hpre : f ⁻¹' S = S := by
    ext z
    simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, hq]
  have hpos : volume S ≠ 0 := (hSo.measure_pos volume ⟨0, by simp [hSdef]⟩).ne'
  have hfin : volume S ≠ ⊤ := by
    have hsub : S ⊆ Metric.ball 0 1 := by
      intro z hz
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro ab
      have h1 : ‖z ab‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ ab)
      have h2 : ∑ i, ‖z i‖ ^ 2 < 1 := hz
      nlinarith [norm_nonneg (z ab)]
    exact ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  have hS := congrArg (fun μ : Measure (PCoord ε → ℂ) => μ S) hmap
  rw [Measure.map_apply hcont.measurable hSo.measurableSet, hpre, Measure.smul_apply, smul_eq_mul] at hS
  have hc : ENNReal.ofReal |(LinearMap.det f)⁻¹| = 1 := by
    have h1 : 1 * volume S = ENNReal.ofReal |(LinearMap.det f)⁻¹| * volume S := by rw [one_mul]; exact hS
    exact ((ENNReal.mul_left_inj hpos hfin).mp h1).symm
  refine ⟨hcont.measurable, ?_⟩
  show Measure.map (⇑f) volume = volume
  rw [hmap, hc, one_smul]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperA
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_integral_exp_norm {c : ℝ} (hc : 0 < c) :
    ∫ x : ℂ, Real.exp (-c * ‖x‖) = Real.pi * c ^ (-2 : ℝ) * Real.Gamma 3 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) le_rfl hc
  have e1 : (-2 / (1 : ℝ)) = -2 := by norm_num
  have e2 : (2 / (1 : ℝ) + 1) = 3 := by norm_num
  simp only [Real.rpow_one, e1, e2] at h
  exact h

theorem fdU_integrable_exp_norm {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℂ => Real.exp (-c * ‖x‖)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_exp_norm hc]
  exact (mul_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hc _))
    (Real.Gamma_pos_of_pos (by norm_num))).ne'

theorem fdU_integral_gauss {b : ℝ} (hb : 0 < b) : ∫ x : ℂ, Real.exp (-b * ‖x‖ ^ 2) = Real.pi / b := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (by norm_num) hb
  have e1 : (-2 / (2 : ℝ)) = -1 := by norm_num
  have e2 : (2 / (2 : ℝ) + 1) = 2 := by norm_num
  simp only [Real.rpow_two, e1, e2, Real.rpow_neg_one, Real.Gamma_two, mul_one] at h
  rw [h, div_eq_mul_inv]

theorem fdU_integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℂ => Real.exp (-b * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_gauss hb]
  exact (div_pos Real.pi_pos hb).ne'

theorem fdU_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  have h : ((ab.1.2 : ℕ) : ℝ) < ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast ab.2.1
  simp only [wab, Pi.zero_apply]
  linarith

theorem exp_neg_quadratic_eq_prod {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab : PCoord ε, Real.exp (-wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2) := by
  simp only [Qf, ← Finset.sum_neg_distrib, Real.exp_sum, neg_mul]

theorem fdU_integrable_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2)) := by
  exact Integrable.fintype_prod
    (f := fun ab (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2)) (fun ab => fdU_integrable_gauss (hb ab))

theorem fdU_integral_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    ∫ y : PCoord ε → ℂ, ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2) = ∏ ab : PCoord ε, Real.pi / b ab := by
  exact (integral_fintype_prod_eq_prod
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2))).trans
    (Finset.prod_congr rfl fun ab _ => fdU_integral_gauss (hb ab))

theorem fdU_lintegral_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hb : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 :=
    fun ab => fdU_wab_zero_pos ab
  have hint : Integrable (fun y : PCoord ε → ℂ => Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
    simp_rw [exp_neg_quadratic_eq_prod]
    exact fdU_integrable_prod_gauss _ hb
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  congr 1
  simp_rw [exp_neg_quadratic_eq_prod]
  rw [fdU_integral_prod_gauss _ hb]
  rfl

theorem fdU_integrable_prod_exp {ε : Fin n → Bool} {c : ℝ} (hc : ∀ _ : PCoord ε, 0 < c) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-c * ‖y ab‖)) := by
  exact Integrable.fintype_prod
    (f := fun _ (x : ℂ) => Real.exp (-c * ‖x‖)) (fun ab => fdU_integrable_exp_norm (hc ab))

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Banach

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem hasDerivAt_exp_comm_add_bracket (A V X : R) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  letI : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ R
  have hdiff : DifferentiableAt ℝ NormedSpace.exp A :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) A).differentiableAt
  have hchain : ∀ B : R, HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • B))
      (fderiv ℝ NormedSpace.exp A B) 0 := by
    intro B
    have hl : HasDerivAt (fun s : ℝ => A + s • B) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hV : fderiv ℝ NormedSpace.exp A V = NormedSpace.exp A * V := by
    have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • V)) (NormedSpace.exp A * V) 0 := by
      have h3 : (fun s : ℝ => NormedSpace.exp (A + s • V)) =
          fun s => NormedSpace.exp A * NormedSpace.exp (s • V) := by
        funext s
        exact NormedSpace.exp_add_of_commute (h.smul_right s)
      rw [h3]
      have h4 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) V (0 : ℝ)).const_mul (NormedSpace.exp A)
      simpa using h4
    exact (hchain V).unique h2
  have hinv : ∀ s : ℝ, NormedSpace.exp (s • X) * NormedSpace.exp (s • (-X)) = 1 ∧
      NormedSpace.exp (s • (-X)) * NormedSpace.exp (s • X) = 1 := by
    intro s
    constructor
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_right),
        add_neg_cancel, NormedSpace.exp_zero]
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_left),
        neg_add_cancel, NormedSpace.exp_zero]
  have hFG : (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))) =
      fun s => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)) := by
    funext s
    exact NormedSpace.exp_units_conj
      ⟨NormedSpace.exp (s • X), NormedSpace.exp (s • (-X)), (hinv s).1, (hinv s).2⟩ A
  have hd1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hd2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hd1 hd2
  have hc : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))
      (X * A - A * X) 0 := by
    have := (hd1.mul_const A).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hF : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)))
      (X * NormedSpace.exp A - NormedSpace.exp A * X) 0 := by
    have := (hd1.mul_const (NormedSpace.exp A)).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hG : HasDerivAt (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X))))
      (fderiv ℝ NormedSpace.exp A (X * A - A * X)) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  rw [hFG] at hG
  have hB : fderiv ℝ NormedSpace.exp A (X * A - A * X) = X * NormedSpace.exp A - NormedSpace.exp A * X :=
    hG.unique hF
  have key := hchain (V + (X * A - A * X))
  rw [map_add (f := _), hV, hB] at key
  exact key

end Banach

section Operator

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_mexp_comm_add_bracket (A V X : Matrix (Fin n) (Fin n) ℂ) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  exact hasDerivAt_exp_comm_add_bracket A V X h

end Operator

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAd {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      ((((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ * W *
        ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j) *
    (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ

private theorem hasDerivAt_exp_conj_diag (U U' : Matrix (Fin n) (Fin n) ℂ) (h1 : U * U' = 1) (h2 : U' * U = 1)
    (x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp
        ((2 : ℂ) • (U * diagonal (fun i => (x i : ℂ)) * U') + (s : ℂ) • W))
      (NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U') *
        (U * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * (U' * W * U) i j) * U') *
        NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U')) 0 := by
  classical
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (x i : ℂ)) with hD
  set W' := U' * W * U with hW'
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (2 * x i : ℂ)) with hA
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => if x i = x j then W' i j else 0) with hV
  set Xm : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => if x i = x j then 0 else W' i j / (2 * (x j : ℂ) - 2 * x i)) with hXm
  have hcomm : Commute A V := by
    show A * V = V * A
    ext i j
    simp only [hA, hV, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true]
      ring
    · simp only [h, if_false, mul_zero, zero_mul]
  have hsplit : V + (Xm * A - A * Xm) = W' := by
    ext i j
    simp only [hA, hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    split_ifs with h
    · simp
    · have h' : (2 * (x j : ℂ) - 2 * x i) ≠ 0 := by
        intro h0
        apply h
        have : ((x i : ℝ) : ℂ) = x j := by linear_combination -h0 / 2
        exact_mod_cast this
      calc _ = W' i j / (2 * (x j : ℂ) - 2 * x i) * (2 * x j - 2 * x i) := by ring
        _ = W' i j := div_mul_cancel₀ _ h'
  have hder := hasDerivAt_mexp_comm_add_bracket A V Xm hcomm
  rw [hsplit] at hder
  have hexpA : NormedSpace.exp A = diagonal (fun i => Complex.exp (2 * x i)) := by
    rw [hA, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hexpD : NormedSpace.exp D = diagonal (fun i => Complex.exp (x i)) := by
    rw [hD, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hval : NormedSpace.exp A * V + (Xm * NormedSpace.exp A - NormedSpace.exp A * Xm) =
      NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D := by
    rw [hexpA, hexpD]
    ext i j
    simp only [hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true, sub_self, shc, if_true, Complex.ofReal_one, mul_zero, zero_mul,
        sub_zero, add_zero, one_mul]
      rw [show (2 * (x j : ℂ)) = x j + x j by ring, Complex.exp_add]
      ring
    · simp only [h, if_false, mul_zero, zero_add]
      have hne : x i - x j ≠ 0 := sub_ne_zero.mpr h
      have hreal : (Real.exp (2 * x j) - Real.exp (2 * x i)) / (2 * x j - 2 * x i) =
          Real.exp (x i) * Real.exp (x j) * (Real.sinh (x i - x j) / (x i - x j)) := by
        have h3 : (2 * x j - 2 * x i) ≠ 0 := by
          intro h0
          apply hne
          linarith
        have ei := Real.exp_pos (x i)
        have ej := Real.exp_pos (x j)
        rw [Real.sinh_eq, Real.exp_neg, Real.exp_sub, two_mul, two_mul, Real.exp_add, Real.exp_add]
        field_simp
        ring
      unfold shc
      rw [if_neg hne]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      push_cast
      calc _ = W' i j * ((Complex.exp (2 * (x j : ℂ)) - Complex.exp (2 * (x i : ℂ))) /
            (2 * (x j : ℂ) - 2 * x i)) := by ring
        _ = _ := by
          rw [hC]
          ring
  rw [hval] at hder

  have hunit : IsUnit U := ⟨⟨U, U', h1, h2⟩, rfl⟩
  have hconjExp : ∀ M : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp (U * M * U') = U * NormedSpace.exp M * U' :=
    fun M => Matrix.exp_units_conj ⟨U, U', h1, h2⟩ M
  have hfun : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • (U * D * U') + (s : ℂ) • W)) =
      fun s : ℝ => U * NormedSpace.exp (A + s • W') * U' := by
    funext s
    rw [← hconjExp]
    congr 1
    have hA2 : A = (2 : ℂ) • D := by
      rw [hA, hD]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hA2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
      Matrix.mul_smul, Matrix.smul_mul, hW']
    congr 1
    rw [show U * (U' * W * U) * U' = (U * U') * W * (U * U') by simp only [Matrix.mul_assoc], h1,
      Matrix.one_mul, Matrix.mul_one]
  have hD2 : U * D * U' = U * diagonal (fun i => (x i : ℂ)) * U' := rfl
  rw [← hD2, hfun]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun M => U * M * U'
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  have hL := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
  have hL' : HasDerivAt (fun s : ℝ => U * NormedSpace.exp (A + s • W') * U')
      (U * (NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D) * U') 0 := hL
  refine hL'.congr_deriv ?_
  rw [hconjExp D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U' U, h2, Matrix.one_mul, ← Matrix.mul_assoc U' U, h2, Matrix.one_mul]

private theorem pmat_spectral {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    pmat y = ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun i => (pev y i : ℂ)) *
      (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  have h := (pmat_isHermitian y).spectral_theorem
  conv_lhs => rw [h]
  first
  | rfl
  | simp [Function.comp_def, Matrix.star_eq_conjTranspose, pev]

theorem hasDerivAt_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W))
      (NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y)) 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU1 : U * Uᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hU2 : Uᴴ * U = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have key := hasDerivAt_exp_conj_diag U Uᴴ hU1 hU2 (pev y) W
  rw [← pmat_spectral y] at key
  exact key

end ReciprocityTheory.ChartRestriction.DS
end
end
