module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartUniformConstantsHalfPolydisc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureFormSelfEqDualNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureFormSelfEqDualNorm
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

namespace GlobalTheory.CurvForm

theorem form_mulVec_left {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K (M *ᵥ v) w = form (Mᵀ * K) v w := by
  simp only [form]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_mulVec_right {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K v (M *ᵥ w) = form (K * Mᴴᵀ) v w := by
  simp only [form]
  rw [star_mulVec, ← mulVec_transpose, mulVec_mulVec]

theorem form_curv_self_eq : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ),
    MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) →
    (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) →
    ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v =
      form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  intro n g H z h2 hu hs hh hdd ξ v
  have hP : (mdel H z ξ)ᵀ = mdel H z ξ := by
    rw [← mdel_transpose, mdel_congr (hs.mono fun x hx => hx.eq)]
  have hQ : mdbar H z ξ = (mdel H z ξ)ᴴ := (conjTranspose_mdel hh ξ).symm
  have hHt : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hHi : (H z)⁻¹ᵀ = (H z)⁻¹ := by rw [transpose_nonsing_inv, hHt]
  rw [curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, hHt, hP, hQ]
  set P := mdel H z ξ with hPdef
  have hPc : Pᴴᵀ = Pᴴ := by
    ext i j
    have := congrFun (congrFun hP i) j
    simp only [transpose_apply, conjTranspose_apply] at this ⊢
    rw [this]
  simp only [form_mulVec_left, form_mulVec_right]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_mul, hHi, hP, transpose_transpose, hPc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

end GlobalTheory.CurvForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureFormSelfEqDualNormStatement
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_form_self_eq_dual_norm : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ), MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) → ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v = form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  first | exact @GlobalTheory.CurvForm.form_curv_self_eq | exact GlobalTheory.CurvForm.form_curv_self_eq | (intros; apply GlobalTheory.CurvForm.form_curv_self_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBound
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeCurvPoint

variable {g : ℕ}

theorem re_form_map (M : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (form (M.map ofReal) v v).re = (fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) := by
  simp only [form_eq_sum, dotProduct, mulVec, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.map_apply, mul_re, mul_im, conj_re, conj_im]; ring

theorem isHermitian_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) :
    (M.map ofReal).IsHermitian := by
  ext i j; simp [conjTranspose_apply, hM.apply]

theorem form_map_self {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) (v : Fin g → ℂ) :
    form (M.map ofReal) v v = (((fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_form_map, ofReal_re]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp (conj_form (isHermitian_map hM) v v)

theorem posSemidef_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) : (M.map ofReal).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_map hM, fun x => ?_⟩
  have e : star x ⬝ᵥ (M.map ofReal) *ᵥ x = form (M.map ofReal) (star x) (star x) := by
    simp [form]
  rw [e, form_map_self hM]
  exact_mod_cast add_nonneg (h _) (h _)

theorem sum_norm_sq (v : Fin g → ℂ) : ∑ j, ‖v j‖ ^ 2 =
    (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by
  simp only [dotProduct, ← Finset.sum_add_distrib, Complex.sq_norm, Complex.normSq_apply]

theorem gnorm_map_star (M : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℂ) :
    gnorm (M.map ofReal) (star u) = gnorm (M.map ofReal) u := by
  have e1 : (fun j => (star u j).re) = fun j => (u j).re := by ext j; simp
  have e2 : (fun j => (star u j).im) = -fun j => (u j).im := by ext j; simp
  rw [gnorm, gnorm, re_form_map, re_form_map, e1, e2, mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

theorem dotProduct_mulVec_eq_form {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsSymm)
    (u v : Fin g → ℂ) : u ⬝ᵥ M *ᵥ v = form M v (star u) := by
  rw [form, star_star, dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

theorem dotProduct_finsetSum {a : ℕ} (u : Fin g → ℂ) (w : Fin a → Fin g → ℂ) :
    u ⬝ᵥ ∑ i, w i = ∑ i, u ⬝ᵥ w i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dual_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K →
    Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) →
    (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) →
    (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  intro g a Y Bs Dm s t c K hc hK hY hcY hB ht hBt hD
  have hBs : ∀ i, (Bs i).IsSymm := fun i =>
    IsSymm.ext fun j k => by simpa using (hB i).isHermitian.apply j k
  have hYpos : ∀ v : Fin g → ℂ, c * ∑ j, ‖v j‖ ^ 2 ≤ (form (Y.map ofReal) v v).re := fun v => by
    rw [re_form_map, sum_norm_sq, mul_add]; exact add_le_add (hcY _) (hcY _)
  have hPD : (Y.map ofReal).PosDef := by
    refine posDef_iff.2 ⟨isHermitian_map hY, fun v hv => ?_⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hS : 0 < ∑ j, ‖v j‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hj) 2⟩
    have h1 := hYpos v
    rw [form_map_self hY] at h1 ⊢
    rw [ofReal_re] at h1
    rw [Complex.zero_lt_real]
    linarith [mul_pos hc hS]
  have hYpsd := hPD.posSemidef
  have hBpsd : ∀ i, ((Bs i).map ofReal).PosSemidef := fun i =>
    posSemidef_map (hBs i) fun x => by simpa using (hB i).dotProduct_mulVec_nonneg x
  have hgB : ∀ i w, t i * gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 :=
    fun i w => by
      rw [gnorm_sq (hBpsd i), gnorm_sq hYpsd, re_form_map, re_form_map, mul_add]
      exact add_le_add (hBt i _) (hBt i _)
  have hgY : ∀ w : Fin g → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 := fun w => by
    rw [gnorm_sq hYpsd]; exact hYpos w
  have hgc : 0 ≤ (g : ℝ) / c := div_nonneg (Nat.cast_nonneg _) hc.le

  have hDb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ Dm *ᵥ v‖ ≤
      g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    have h1 : ‖u ⬝ᵥ Dm *ᵥ v‖ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := by
      simp only [dotProduct, mulVec]
      calc _ ≤ ∑ j, ‖u j * ∑ k, Dm j k * v k‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖u j‖ * ∑ k, K * ‖v k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD j k) (norm_nonneg _)
        _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    have hs : ∀ w : Fin g → ℂ, (∑ j, ‖w j‖) ^ 2 ≤ g / c * gnorm (Y.map ofReal) w ^ 2 :=
      fun w => by
        refine sq_sum_le_card_mul_sum_sq.trans ?_
        rw [Finset.card_univ, Fintype.card_fin, div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith [hgY w, (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    have hab : (∑ j, ‖u j‖) * (∑ k, ‖v k‖) ≤
        g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      rw [← pow_le_pow_iff_left₀ (by positivity)
        (mul_nonneg (mul_nonneg hgc (gnorm_nonneg _ _)) (gnorm_nonneg _ _)) two_ne_zero]
      calc ((∑ j, ‖u j‖) * (∑ k, ‖v k‖)) ^ 2 = (∑ j, ‖u j‖) ^ 2 * (∑ k, ‖v k‖) ^ 2 := mul_pow _ _ _
        _ ≤ (g / c * gnorm (Y.map ofReal) u ^ 2) * (g / c * gnorm (Y.map ofReal) v ^ 2) :=
          mul_le_mul (hs u) (hs v) (sq_nonneg _) (mul_nonneg hgc (sq_nonneg _))
        _ = _ := by ring
    calc _ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := h1
      _ ≤ K * (g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v) :=
        mul_le_mul_of_nonneg_left hab hK
      _ = _ := by ring

  have hBb : ∀ i (u v : Fin g → ℂ), ‖u ⬝ᵥ (Bs i).map ofReal *ᵥ v‖ ≤
      gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i := by
    intro i u v
    rw [dotProduct_mulVec_eq_form ((hBs i).map _)]
    refine (norm_form_le (hBpsd i) _ _).trans ?_
    rw [gnorm_map_star]
    rw [← pow_le_pow_iff_left₀ (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _))
      (div_nonneg (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)) (ht i).le) two_ne_zero]
    have a1 : ∀ w, gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 / t i := fun w => by
      rw [le_div_iff₀ (ht i), mul_comm]; exact hgB i w
    calc (gnorm ((Bs i).map ofReal) v * gnorm ((Bs i).map ofReal) u) ^ 2 =
          gnorm ((Bs i).map ofReal) v ^ 2 * gnorm ((Bs i).map ofReal) u ^ 2 := mul_pow _ _ _
      _ ≤ (gnorm (Y.map ofReal) v ^ 2 / t i) * (gnorm (Y.map ofReal) u ^ 2 / t i) :=
          mul_le_mul (a1 v) (a1 u) (sq_nonneg _) (div_nonneg (sq_nonneg _) (ht i).le)
      _ = _ := by ring

  have hPb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    rw [add_mulVec, sum_mulVec, dotProduct_add, dotProduct_finsetSum]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ i, u ⬝ᵥ (s i • (Bs i).map ofReal) *ᵥ v‖ ≤
        ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul]
      calc _ ≤ ‖s i‖ * (gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i) :=
            mul_le_mul_of_nonneg_left (hBb i u v) (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v +
          ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v :=
          add_le_add (hDb u v) h2
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

  refine ⟨hPD, fun v => ?_⟩
  have hdet : IsUnit (Y.map ofReal).det := (isUnit_iff_isUnit_det _).1 hPD.isUnit
  set x := (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v with hx
  set q := (Y.map ofReal)⁻¹ *ᵥ star x with hq
  have hF : form (Y.map ofReal)⁻¹ x x = q ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v := by
    rw [form]; exact dotProduct_comm _ _
  have hsq : star q = (Y.map ofReal)⁻¹ *ᵥ x := by
    rw [hq, star_mulVec, star_star, (isHermitian_map hY).inv.eq, ← mulVec_transpose,
      transpose_nonsing_inv, (hY.map _).eq]
  have hq2 : gnorm (Y.map ofReal) q ^ 2 = (form (Y.map ofReal)⁻¹ x x).re := by
    rw [gnorm_sq hYpsd]
    simp only [form]
    rw [hsq, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]
  have hb := hPb q v
  rw [← hF] at hb
  have hre : gnorm (Y.map ofReal) q ^ 2 ≤ ‖form (Y.map ofReal)⁻¹ x x‖ := hq2 ▸ re_le_norm _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rcases (norm_nonneg (form (Y.map ofReal)⁻¹ x x)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_right ?_ h0
    calc ‖form (Y.map ofReal)⁻¹ x x‖ * ‖form (Y.map ofReal)⁻¹ x x‖ =
          ‖form (Y.map ofReal)⁻¹ x x‖ ^ 2 := by ring
      _ ≤ _ := h2
      _ = (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map ofReal) v ^ 2 *
          gnorm (Y.map ofReal) q ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (by positivity)

end GlobalTheory.HodgeCurvPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBoundStatement
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K → Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) → (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) → (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹ ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v) ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤ (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  first | exact @GlobalTheory.HodgeCurvPoint.dual_bound | exact GlobalTheory.HodgeCurvPoint.dual_bound | (intros; apply GlobalTheory.HodgeCurvPoint.dual_bound <;> assumption)
end
end

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeChartRow

theorem smulMulVec {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] (c : R) (A : Matrix m m R)
    (x : m → R) : (c • A) *ᵥ x = c • (A *ᵥ x) := by
  ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem quad_decomp {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (t : Fin a → ℝ) (x : Fin g → ℝ) :
    x ⬝ᵥ (A + ∑ i, t i • Bs i) *ᵥ x = x ⬝ᵥ A *ᵥ x + ∑ i, t i * (x ⬝ᵥ Bs i *ᵥ x) := by
  rw [add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smulMulVec, dotProduct_smul, smul_eq_mul]

theorem isOpen_polydisc (n : ℕ) (ρ : ℝ) : IsOpen (polydisc n ρ) := by
  simp only [polydisc, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const

theorem isOpen_punctured {n a : ℕ} (ha : a ≤ n) (ρ : ℝ) : IsOpen (punctured ha ρ) := by
  have : punctured ha ρ = polydisc n ρ ∩ ⋂ i : Fin a, {z : Fin n → ℂ | z (Fin.castLE ha i) ≠ 0} := by
    ext z; simp [punctured]
  rw [this]
  exact (isOpen_polydisc n ρ).inter
    (isOpen_iInter_of_finite fun i => isOpen_ne_fun (by fun_prop) continuous_const)

theorem hodgeChartBounds_of_schur_lemW (hS : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z) (hW : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖) : HodgeChartBounds := by
  intro n a g rk ha τ₀ B hP
  obtain ⟨T₀, c₁, C₁, M, β, hT₀, hc₁, hM, hβ, hBq, hY'⟩ := GlobalTheory.T.periodChart_uniform_constants_half_polydisc n a g rk τ₀ B hS hP
  obtain ⟨W, hW'⟩ := hW g a (fun i => (B i).map (Int.cast : ℤ → ℝ)) c₁ C₁ hc₁ hP.psd
  have hBnn : ∀ i (x : Fin g → ℝ), 0 ≤ x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x := fun i x => by
    simpa using (posSemidef_iff_dotProduct_mulVec.1 (hP.psd i)).2 x
  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  set W' : ℝ := max W 0 with hW'def
  set ρ : ℝ := min (1 / 2) (Real.exp (-(4 * Real.pi * T₀))) with hρ
  have hρ0 : 0 < ρ := lt_min (by norm_num) (Real.exp_pos _)
  have hρ2 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := hρ2.trans (by norm_num)

  have hsymR : ∀ x ∈ polydisc n 1, (imPeriod ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm x hx).apply]
  have hsymC : ∀ x ∈ polydisc n 1, (hodgeGram ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [hodgeGram, (hsymR x hx).apply j k]
  have hhermC : ∀ x ∈ polydisc n 1, (hodgeGram ha τ₀ B x).IsHermitian := fun x hx => by
    ext j k; simp [hodgeGram, conjTranspose_apply, (hsymR x hx).apply j k]

  have hz1 : ∀ z ∈ punctured ha ρ, z ∈ punctured ha 1 := fun z hz =>
    ⟨fun k => (hz.1 k).trans_le hρ1, hz.2⟩
  have hzh : ∀ z ∈ punctured ha ρ, z ∈ polydisc n (1 / 2) := fun z hz k => (hz.1 k).trans_le hρ2
  have ht : ∀ z ∈ punctured ha ρ, ∀ i : Fin a, 2 * T₀ < tlog (z (Fin.castLE ha i)) := by
    intro z hz i
    have h0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
    have h1 : ‖z (Fin.castLE ha i)‖ < Real.exp (-(4 * Real.pi * T₀)) :=
      (hz.1 _).trans_le (min_le_right _ _)
    have h2 : Real.log ‖z (Fin.castLE ha i)‖ < -(4 * Real.pi * T₀) := by
      rw [← Real.log_exp (-(4 * Real.pi * T₀))]; exact Real.log_lt_log h0 h1
    rw [tlog, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hdec : ∀ z, imPeriod ha τ₀ B z = ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ))
      + ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) • (B i).map (Int.cast : ℤ → ℝ) := fun z => by
    simp only [imPeriod, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]; abel

  have hq : ∀ z (x : Fin g → ℝ), x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x =
      x ⬝ᵥ ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x
      + ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) :=
    fun z x => by rw [hdec z, quad_decomp]
  have hYlow : ∀ z ∈ punctured ha ρ, ∀ x, c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x := by
    intro z hz x
    rw [hq]
    have := ((hY' z (hzh z hz)).2.1 x)
    have : 0 ≤ ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [ht z hz i]) (hBnn i x)
    linarith
  have hYBi : ∀ z ∈ punctured ha ρ, ∀ i (x : Fin g → ℝ), (tlog (z (Fin.castLE ha i)) - T₀) *
      (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) ≤ x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x := by
    intro z hz i x
    rw [hq]
    have h1 := ((hY' z (hzh z hz)).2.1 x)
    have h2 : 0 ≤ x ⬝ᵥ x := by simpa [dotProduct] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j)
    have h3 := Finset.single_le_sum (f := fun i => (tlog (z (Fin.castLE ha i)) - T₀) *
      (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x))
      (fun i _ => mul_nonneg (by linarith [ht z hz i]) (hBnn i x)) (Finset.mem_univ i)
    nlinarith

  set K₁ : ℝ := 2 * g * M / c₁ + a with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set C : ℝ := max (max C₁ β) (max (g * (2 * g * M / c₁ + W' * a)) (2 * (1 / 4 * K₁ ^ 2))) with hC
  refine ⟨ρ, c₁, C, hρ0, hρ2, hc₁, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    have hs : (imPeriod ha τ₀ B z - c₁ • (1 : Matrix (Fin g) (Fin g) ℝ)).IsSymm :=
      (hsymR z (hz1 z hz).1).sub (isSymm_one.smul c₁)
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hs
    · simp only [star_trivial, sub_mulVec, smulMulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      linarith [hYlow z hz x]
  ·
    intro z hz
    set S : ℝ := ∑ i : Fin a, tlog (z (Fin.castLE ha i))
    have hs : ((C * (1 + S)) • (1 : Matrix (Fin g) (Fin g) ℝ) - imPeriod ha τ₀ B z).IsSymm :=
      (isSymm_one.smul _).sub (hsymR z (hz1 z hz).1)
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hs
    · simp only [star_trivial, sub_mulVec, smulMulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hq]
      have h2 : 0 ≤ x ⬝ᵥ x := by simpa [dotProduct] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j)
      have h1 := (hY' z (hzh z hz)).2.2.1 x
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by linarith [ht z hz i]
      have h3 : ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x)
          ≤ S * (β * (x ⬝ᵥ x)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        have := hBq i x
        have := hBnn i x
        have := ht z hz i
        nlinarith
      have hC1 : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
      have hCβ : β ≤ C := (le_max_right _ _).trans (le_max_left _ _)
      nlinarith [mul_le_mul_of_nonneg_right hC1 h2,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCβ h2) hS0]
  ·
    intro z hz
    have hzp := hz1 z hz
    obtain ⟨hGpsd, hG⟩ := GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz
    refine ⟨PosDef.one, hGpsd, fun ξ => ?_⟩
    have hgn0 : 0 ≤ gnorm (poincareGram a z) ξ := gnorm_nonneg _ _
    obtain ⟨hξk, hξi⟩ := hG ξ
    have hξ : ‖ξ‖ ≤ 2 * gnorm (poincareGram a z) ξ := (pi_norm_le_iff_of_nonneg (by positivity)).2 hξk
    rw [conn_hodgeGram ha hP hzp.1 ξ, (GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z hzp).2.1 ξ]
    have ht'0 : ∀ i, 0 < (fun i => tlog (z (Fin.castLE ha i)) - T₀) i := fun i => by
      simp only; linarith [ht z hz i]
    have hWY : ∀ i x, ‖((fun i => tlog (z (Fin.castLE ha i)) - T₀) i • ((imPeriod ha τ₀ B z)⁻¹ *
        (fun i => (B i).map (Int.cast : ℤ → ℝ)) i)) *ᵥ x‖ ≤ W' * ‖x‖ := by
      intro i x
      have := hW' _ (fun i => tlog (z (Fin.castLE ha i)) - T₀) (hY' z (hzh z hz)).1
        (hY' z (hzh z hz)).2.1 (hY' z (hzh z hz)).2.2.1 ht'0 i x
      beta_reduce at this ⊢
      rw [← hdec z] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have key := GlobalTheory.T.connectionMatrix_gramOperatorNorm_le g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ))
      (of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ)
      (fun i => ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i)))
      (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ (M * ‖ξ‖) W'
      hc₁ (by positivity) (le_max_right _ _) (hYlow z hz) ht'0 hWY
      (fun j k => by simpa using (hY' z (hzh z hz)).2.2.2 j k ξ)
    refine key.trans ?_
    have hs : ∀ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ gnorm (poincareGram a z) ξ := by
      intro i
      have hz0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
      have htt := ht z hz i
      have hpi := Real.pi_gt_three
      have e : ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ =
          ‖ξ (Fin.castLE ha i)‖ / (2 * Real.pi * ‖z (Fin.castLE ha i)‖) := by
        rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]; norm_num
      rw [e, div_div, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
      have h1 := hξi i
      have h2 : tlog (z (Fin.castLE ha i)) ≤ Real.pi * (tlog (z (Fin.castLE ha i)) - T₀) := by
        nlinarith
      calc ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) *
            gnorm (poincareGram a z) ξ := h1
        _ ≤ 2 * (‖z (Fin.castLE ha i)‖ * (Real.pi * (tlog (z (Fin.castLE ha i)) - T₀))) *
            gnorm (poincareGram a z) ξ := by gcongr
        _ = _ := by ring
    have hsum : ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ a * gnorm (poincareGram a z) ξ := by
      refine (Finset.sum_le_sum fun i _ => hs i).trans ?_
      simp
    have hC3 : g * (2 * g * M / c₁ + W' * a) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have hW0 : 0 ≤ W' := le_max_right _ _
    calc (g : ℝ) * (g * (M * ‖ξ‖) / c₁ + W' * ∑ i, ‖ξ (Fin.castLE ha i) /
          (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀))
        ≤ g * (g * (M * (2 * gnorm (poincareGram a z) ξ)) / c₁ + W' * (a * gnorm (poincareGram a z) ξ)) := by
          gcongr
      _ = (g * (2 * g * M / c₁ + W' * a)) * gnorm (poincareGram a z) ξ := by ring
      _ ≤ C * gnorm (poincareGram a z) ξ := by gcongr
  ·
    have hC' : 0 ≤ 1 / 4 * K₁ ^ 2 := by positivity
    have hPD : ∀ z ∈ punctured ha ρ, ((imPeriod ha τ₀ B z).map Complex.ofReal).PosDef := fun z hz =>
      (GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ)) 0 0
        (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ 0 hc₁ le_rfl (hsymR z (hz1 z hz).1) (hYlow z hz)
        hP.psd (fun i => show 0 < tlog _ - T₀ by linarith [ht z hz i]) (hYBi z hz) (fun j k => by simp)).1
    have hPos : IsPosFrame (punctured ha ρ) (hodgeGram ha τ₀ B) := ⟨isOpen_punctured ha ρ,
      fun j k z hz => ((GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z (hz1 z hz)).1 j k).contDiffWithinAt, hPD⟩
    refine (twoFormBound_curv_two_mul hPos (fun z hz => (GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz).1) hC' ?_).mono
      ((le_max_right _ _).trans (le_max_right _ _))
    intro z hz ξ v
    have hzp := hz1 z hz
    obtain ⟨hB1, hB2, hB3⟩ := GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z hzp
    obtain ⟨hGpsd, hG⟩ := GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz
    have hpd := hPD z hz
    have hgn0 : 0 ≤ gnorm (poincareGram a z) ξ := gnorm_nonneg _ _
    obtain ⟨hξk, hξi⟩ := hG ξ
    have hξ : ‖ξ‖ ≤ 2 * gnorm (poincareGram a z) ξ := (pi_norm_le_iff_of_nonneg (by positivity)).2 hξk
    rw [GlobalTheory.T.chernCurvature_form_self_eq_dual_norm n g (hodgeGram ha τ₀ B) z (hB1.of_le (by norm_cast))
      ((isUnit_iff_isUnit_det _).1 hpd.isUnit)
      (mem_of_superset ((isOpen_polydisc n 1).mem_nhds hzp.1) fun x hx => hsymC x hx)
      (mem_of_superset ((isOpen_polydisc n 1).mem_nhds hzp.1) fun x hx => hhermC x hx) hB3 ξ v,
      hB2 ξ, smulMulVec, form_smul_left, form_smul_right]
    obtain ⟨-, hbd⟩ := GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ))
      (of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ)
      (fun i => ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i)))
      (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ (M * ‖ξ‖) hc₁ (by positivity)
      (hsymR z hzp.1) (hYlow z hz) hP.psd (fun i => show 0 < tlog _ - T₀ by linarith [ht z hz i]) (hYBi z hz)
      (fun j k => by simpa using (hY' z (hzh z hz)).2.2.2 j k ξ)
    have hbd' := hbd v
    beta_reduce at hbd'
    have hs : ∀ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ gnorm (poincareGram a z) ξ := by
      intro i
      have hz0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
      have htt := ht z hz i
      have hpi := Real.pi_gt_three
      have e : ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ =
          ‖ξ (Fin.castLE ha i)‖ / (2 * Real.pi * ‖z (Fin.castLE ha i)‖) := by
        rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]; norm_num
      rw [e, div_div, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
      have h1 := hξi i
      have h2 : tlog (z (Fin.castLE ha i)) ≤ Real.pi * (tlog (z (Fin.castLE ha i)) - T₀) := by
        nlinarith
      calc ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) *
            gnorm (poincareGram a z) ξ := h1
        _ ≤ 2 * (‖z (Fin.castLE ha i)‖ * (Real.pi * (tlog (z (Fin.castLE ha i)) - T₀))) *
            gnorm (poincareGram a z) ξ := by gcongr
        _ = _ := by ring
    have hsum : ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ a * gnorm (poincareGram a z) ξ := by
      refine (Finset.sum_le_sum fun i _ => hs i).trans ?_
      simp
    have hsum0 : 0 ≤ ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) :=
      Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (by linarith [ht z hz i])
    have hK : g * (M * ‖ξ‖) / c₁ + ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I *
        z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀) ≤ K₁ * gnorm (poincareGram a z) ξ := by
      calc _ ≤ g * (M * (2 * gnorm (poincareGram a z) ξ)) / c₁ + a * gnorm (poincareGram a z) ξ := by
            gcongr
        _ = K₁ * gnorm (poincareGram a z) ξ := by rw [hK₁]; ring
    have hnc : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hnc]
    simp only [hodgeGram]
    have hX0 : 0 ≤ g * (M * ‖ξ‖) / c₁ + ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I *
        z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀) := by positivity
    have hsq := pow_le_pow_left₀ hX0 hK 2
    have hv0 : 0 ≤ gnorm (hodgeGram ha τ₀ B z) v ^ 2 := sq_nonneg _
    have hv0' : 0 ≤ gnorm ((imPeriod ha τ₀ B z).map Complex.ofReal) v ^ 2 := sq_nonneg _
    have hstep := mul_le_mul_of_nonneg_right hsq hv0'
    nlinarith [hbd', hstep]

end GlobalTheory.HodgeChartRow
