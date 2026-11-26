module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSumma
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGram
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGram
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGramStatement
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  first | exact @GlobalTheory.RealGram.curv_inv_of_real | exact GlobalTheory.RealGram.curv_inv_of_real | (intros; apply GlobalTheory.RealGram.curv_inv_of_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFive
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFive
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.PoinLen

theorem mem_castLE_iff {n a : ℕ} (ha : a ≤ n) (k : Fin n) :
    k ∈ Finset.univ.map (Fin.castLEEmb ha) ↔ k.val < a := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    simp
  · intro h
    exact Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem gnorm_poincareGram_single {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) :
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a z) (Pi.single k 1) =
      √(if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (z k) ^ 2)) else 1 / 2) := by
  rw [GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]
  simp only [Complex.ofReal_re]

theorem sqrt_two_mul_pi_le : √(2 * Real.pi ^ 2) ≤ 5 := by
  rw [show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem gnorm_mul_poinWt_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
    v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n,
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) *
      GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  intro n a ha ρ hρ v hv k
  rw [gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]
  by_cases hk : k.val < a
  · rw [if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]
    have h0 : v.ofLp k ≠ 0 := by
      have := hv.2 ⟨k.val, hk⟩
      simpa [Fin.castLE] using this
    have h1 : ‖v.ofLp k‖ < 1 := lt_of_lt_of_le (hv.1 k) (by linarith)
    have ht := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
    have hx : 0 < ‖v.ofLp k‖ := norm_pos_iff.2 h0
    have hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) := by
      rw [abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
      field_simp
    change √(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) *
      (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5
    rw [hlog]
    set x := ‖v.ofLp k‖
    set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)
    have hB : 0 ≤ x * (2 * Real.pi * t) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    convert sqrt_two_mul_pi_le using 2
    field_simp
  · rw [if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]
    calc √(1 / 2 : ℝ) ≤ √1 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ 5 := by rw [Real.sqrt_one]; norm_num

end GlobalTheory.PoinLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFiveStatement
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n, GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) * GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  first | exact @GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | exact GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | (intros; apply GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwo
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo

theorem tlog_sum_eq_and_log_two_le : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  intro n a ha ρ hρ v hv
  have hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖ := fun i => norm_pos_iff.2 (hv.2 i)
  have hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2 := fun i =>
    lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ
  have hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0 := fun i =>
    Real.log_neg (hpos i) (by linarith [hlt i])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
    rw [abs_of_neg (hneg i)]
  · rw [Finset.sum_map]
    have hs := Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))
    refine le_trans ?_ hs
    have e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ :=
      abs_of_neg (hneg _)
    simp only [] at e ⊢
    rw [e]
    have hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2) :=
      Real.log_le_log (hpos _) (hlt _).le
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith

end GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwoStatement
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  first | exact @GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | exact GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | (intros; apply GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidef
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidef
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem inv_entry_norm_le_of_sub_posSemidef (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ)
    (hc : 0 < c) (hY : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (i j : Fin g) :
    ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by

  have hq : ∀ x : Fin g → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
    intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    linarith

  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hYv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hq v
    rw [hYv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_star_nonneg v]) (by
      simpa using dotProduct_self_star_nonneg v)
    exact hv (by simpa using h2)
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet

  have hmap : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [show Y.map Complex.ofReal = Y.map Complex.ofRealHom from rfl,
      show Y⁻¹.map Complex.ofReal = Y⁻¹.map Complex.ofRealHom from rfl, ← Matrix.map_mul, hYinv]
    simp
  rw [hmap, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]

  set w : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single j 1 with hw
  have hYw : Y *ᵥ w = Pi.single j 1 := by
    rw [hw, mulVec_mulVec, hYinv, one_mulVec]
  have hwi : ∀ k, w k = Y⁻¹ k j := by
    intro k; simp [hw, mulVec_single_one]
  have hqw : c * (w ⬝ᵥ w) ≤ w j := by
    have := hq w
    rw [hYw, dotProduct_single, mul_one] at this
    exact this
  have hsq : ∀ k, w k ^ 2 ≤ w ⬝ᵥ w := by
    intro k
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun l => w l * w l) (fun l _ => mul_self_nonneg (w l))
      (Finset.mem_univ k)
    simpa [sq] using this
  have hj1 := hsq j
  have hi1 := hsq i
  have hwj0 : 0 ≤ w j := by nlinarith [sq_nonneg (w j)]
  have hcwj : c * w j ≤ 1 := by
    rcases hwj0.lt_or_eq with h | h
    · nlinarith
    · rw [← h]; linarith
  have hci1 : c * w i ^ 2 ≤ w j := le_trans (mul_le_mul_of_nonneg_left hi1 hc.le) hqw
  have hci : (c * w i) ^ 2 ≤ 1 := by
    calc (c * w i) ^ 2 = c * (c * w i ^ 2) := by ring
      _ ≤ c * w j := mul_le_mul_of_nonneg_left hci1 hc.le
      _ ≤ 1 := hcwj
  have habs : |c * w i| ≤ 1 := sq_le_one_iff_abs_le_one _ |>.1 hci
  rw [← hwi i, le_div_iff₀ hc]
  rw [abs_mul, abs_of_pos hc] at habs
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidefStatement
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by
  first | exact @GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | exact GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | (intros; apply GlobalTheory.inv_entry_norm_le_of_sub_posSemidef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem psd_real_quad_single (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by
  have h := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
    single_dotProduct, dotProduct_single] at h
  simp [Pi.single_apply, hij, hij.symm] at h
  linarith

theorem abs_entry_le_of_psd_le (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ)
    (hY : Y.PosSemidef) (hMY : (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (i j : Fin g) :
    |Y i j| ≤ M := by
  have hdiag : ∀ k, Y k k ≤ M := by
    intro k
    have := hMY.diag_nonneg (i := k)
    simp at this
    linarith
  have hsym : Y j i = Y i j := by
    have := congrFun (congrFun hY.isHermitian j) i
    simpa [conjTranspose_apply] using this.symm
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hY.diag_nonneg (i := i))]
    exact hdiag i
  · have h1 := psd_real_quad_single g Y hY i j hij 1
    have h2 := psd_real_quad_single g Y hY i j hij (-1)
    have hi := hdiag i
    have hj := hdiag j
    rw [hsym] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith

theorem det_map_ofReal_norm_le : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  intro g Y M _ hY hMY
  have hmap : (Y.map Complex.ofReal).det = ((Y.det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom Y
    exact this.symm
  rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := M) (A := Y)
    (fun i j => abs_entry_le_of_psd_le g Y M hY hMY i j)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPowStatement
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChart
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem conn_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E) (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ : E) : conn (fun x => (H x)⁻¹) z ξ = -(conn H z ξ)ᵀ := by
  rw [conn_congr (H' := fun x => dualGram (H x))
    (hs.mono fun x hx => by simp only [dualGram, transpose_nonsing_inv, hx.eq]) ξ, conn_dual h hu]

theorem norm_mul_apply_le {g : ℕ} (P Q : Matrix (Fin g) (Fin g) ℂ) (p q : ℝ) (hP : ∀ i j, ‖P i j‖ ≤ p)
    (hQ : ∀ i j, ‖Q i j‖ ≤ q) (i j : Fin g) : ‖(P * Q) i j‖ ≤ g * (p * q) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin g)), ‖P i k * Q k j‖ ≤ p * q := fun k _ => by
    rw [norm_mul]
    exact mul_le_mul (hP i k) (hQ k j) (norm_nonneg _) ((norm_nonneg _).trans (hP i k))
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  simp

theorem ofLp_coordVec {n : ℕ} (k : Fin n) : (coordVec k).ofLp = Pi.single k (1 : ℂ) := by simp

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.HermFrame

theorem norm_apply_le_opNorm {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    ‖A i j‖ ≤ opNorm 1 1 A := by
  have h := gnorm_mulVec_le (PosDef.one (n := Fin g) (R := ℂ)) PosSemidef.one A (Pi.single j 1)
  have h1 : gnorm (1 : Matrix (Fin g) (Fin g) ℂ) (Pi.single j 1) = 1 := by
    rw [gnorm, form_single]; simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  set w := A *ᵥ Pi.single j 1 with hw
  have hwi : w i = A i j := by simp [hw, mulVec_single_one]
  rw [gnorm, form, one_mulVec, ← hwi]
  apply Real.le_sqrt_of_sq_le
  have e : w ⬝ᵥ star w = ∑ k, ((‖w k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem inv_hodgeGram_goodBound : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  intro n a ha g rk τ₀ B hP
  obtain ⟨ρ, c₀, C, hρ0, hρ2, hc₀, h1, h2, h3, h4⟩ :=
    GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW GlobalTheory.T.schur_complement_block_quadratic_lower_bound GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec n a g rk ha τ₀ B hP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set D : ℝ := C' * (1 + 1 / Real.log 2 + 1 / (2 * Real.pi)) with hD
  have hD0 : 0 ≤ D := mul_nonneg hC'0 (by positivity)
  set c : ℝ := max (max ((1 / c₀) * (1 / Real.log 2) ^ g) ((g.factorial : ℝ) * D ^ g))
    (max (5 * C') (50 * g * C' ^ 2)) with hc
  refine ⟨ρ, hρ0, hρ2, c, if a = 0 then 0 else g, fun v hv => ?_⟩
  set z : Fin n → ℂ := v.ofLp with hzdef
  set S : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb ha) with hS
  set Y := hodgeGram ha τ₀ B with hY
  set Yv : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ := fun u => Y u.ofLp with hYv
  set s : ℝ := ∑ k ∈ S, |Real.log ‖v k‖| with hs
  have hz1 : z ∈ punctured ha 1 := ⟨fun k => (hv.1 k).trans_le (hρ2.trans (by norm_num)), hv.2⟩
  have hpd : (Y z).PosDef := (h4 z hv).1
  have hu : IsUnit (Y z).det := (isUnit_iff_isUnit_det _).1 hpd.isUnit
  obtain ⟨hYinf, -, hdd⟩ := GlobalTheory.HodgeGramLocal.hodgeGram_local n a g rk ha τ₀ B hP z hz1

  let φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hφ : ∀ u, φ u = u.ofLp := fun u => rfl
  have hφd : ∀ ξ, fderiv ℂ φ v ξ = ξ.ofLp := fun ξ => by rw [φ.fderiv]; rfl
  have hY2 : MContDiffAt 2 Y z := hYinf.of_le (by norm_cast)
  have hYv2 : MContDiffAt 2 Yv v := fun i j =>
    (hY2 i j).comp v ((φ.restrictScalars ℝ).contDiff.contDiffAt)

  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  have hsymR : ∀ x ∈ polydisc n 1, (imPeriod ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm x hx).apply]
  have hnb : ∀ᶠ u in 𝓝 v, u.ofLp ∈ polydisc n 1 :=
    φ.continuous.continuousAt.eventually_mem ((GlobalTheory.HodgeChartRow.isOpen_polydisc n 1).mem_nhds hz1.1)
  have hevS : ∀ᶠ u in 𝓝 v, (Yv u).IsSymm := hnb.mono fun u hu' =>
    IsSymm.ext fun j k => by simp [Yv, Y, hodgeGram, (hsymR _ hu').apply j k]
  have hevH : ∀ᶠ u in 𝓝 v, (Yv u).IsHermitian := hnb.mono fun u hu' => by
    ext j k; simp [Yv, Y, hodgeGram, conjTranspose_apply, (hsymR _ hu').apply j k]
  have hddv : ∀ ξ η, mddbar Yv v ξ η = 0 := fun ξ η => by
    ext i j
    have := GlobalTheory.ddbar_comp_holo (u := fun x => Y x i j) (φ := φ) (z := v) (hY2 i j) φ.contDiff.contDiffAt ξ η
    simp only [mddbar_apply]
    rw [show (fun x => Yv x i j) = fun x => Y (φ x) i j from rfl, this, hφd, hφd]
    have h0 := congrFun (congrFun (hdd ξ.ofLp η.ofLp) i) j
    simp only [mddbar_apply] at h0
    exact h0
  have hconn : ∀ ξ, conn Yv v ξ = conn Y z ξ.ofLp := fun ξ => by
    rw [show Yv = fun x => Y (φ x) from rfl, conn_comp_holo (hY2.of_le (by norm_num)) φ.differentiableAt ξ, hφd]
    rfl

  set Kf : Fin n → ℝ := fun k => C' * gnorm (poincareGram a z) (Pi.single k 1) with hKf
  have hKf0 : ∀ k, 0 ≤ Kf k := fun k => mul_nonneg hC'0 (gnorm_nonneg _ _)
  have hKe : ∀ k i j, ‖conn Y z (Pi.single k 1) i j‖ ≤ Kf k := fun k i j =>
    (norm_apply_le_opNorm _ i j).trans (((h3 z hv).2.2 _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _)))
  have hw0 : ∀ k, 0 ≤ poinWt S v k := fun k => by
    unfold poinWt; split_ifs <;> positivity
  have hKw : ∀ k, Kf k * poinWt S v k ≤ 5 * C' := fun k => by
    have h5 := GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five n a ha ρ hρ2 v hv k
    calc Kf k * poinWt S v k = C' * (gnorm (poincareGram a z) (Pi.single k 1) * poinWt S v k) := by
          simp only [hKf]; ring
      _ ≤ C' * 5 := mul_le_mul_of_nonneg_left h5 hC'0
      _ = 5 * C' := by ring
  have hCe : ∀ k i j, ‖conn Yv v (coordVec k) i j‖ ≤ Kf k := fun k i j => by
    rw [hconn, ofLp_coordVec]; exact hKe k i j
  have hcG : ∀ ξ, conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ = -(conn Yv v ξ)ᵀ :=
    conn_inv Yv v (hYv2.of_le one_le_two) hu hevS
  have hcurvG : ∀ ξ η, curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ η =
      -((conn Yv v η)ᵀᴴ * conn Yv v ξ)ᵀ := GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram Yv v hYv2 hu hevS hevH hddv
  have hdelG : ∀ ξ η, mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x η) v ξ -
      mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x ξ) v η =
      -(conn Yv v η * conn Yv v ξ - conn Yv v ξ * conn Yv v η)ᵀ := GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram Yv v hYv2 hu hevS

  obtain ⟨hts, hlog⟩ := GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo n a ha ρ hρ2 v hv
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc0 : 0 ≤ c := (by positivity : (0:ℝ) ≤ 5 * C').trans ((le_max_left _ _).trans (le_max_right _ _))
  have hcA : (1 / c₀) * (1 / Real.log 2) ^ g ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hcB : (g.factorial : ℝ) * D ^ g ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hc5 : 5 * C' ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hc50 : 50 * g * C' ^ 2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hE : 1 / c₀ ≤ c * s ^ (if a = 0 then 0 else g) ∧
      (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ c * s ^ (if a = 0 then 0 else g) := by
    by_cases ha0 : a = 0
    · rw [if_pos ha0, pow_zero, mul_one]
      have hs' : s / (2 * Real.pi) = 0 := by rw [← hts]; subst ha0; simp
      refine ⟨?_, ?_⟩
      · refine le_trans ?_ hcA
        have : (1 : ℝ) ≤ (1 / Real.log 2) ^ g := one_le_pow₀ (by rw [le_div_iff₀ hl2]; linarith)
        have hc1 : 0 ≤ 1 / c₀ := by positivity
        nlinarith
      · rw [hs', add_zero, mul_one]
        refine le_trans ?_ hcB
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC'0 ?_ g) (Nat.cast_nonneg _)
        rw [hD]
        have : (1 : ℝ) ≤ 1 + 1 / Real.log 2 + 1 / (2 * Real.pi) := by
          have : 0 ≤ 1 / Real.log 2 := by positivity
          have : 0 ≤ 1 / (2 * Real.pi) := by positivity
          linarith
        nlinarith
    · rw [if_neg ha0]
      have hs2 : Real.log 2 ≤ s := hlog (Nat.pos_of_ne_zero ha0)
      refine ⟨?_, ?_⟩
      · calc 1 / c₀ = ((1 / c₀) * (1 / Real.log 2) ^ g) * Real.log 2 ^ g := by
              rw [mul_assoc, ← mul_pow, one_div_mul_cancel hl2.ne', one_pow, mul_one]
          _ ≤ c * s ^ g := mul_le_mul hcA (pow_le_pow_left₀ hl2.le hs2 g) (by positivity) hc0
      · have h1s : 1 ≤ s / Real.log 2 := (one_le_div hl2).2 hs2
        have hM : C' * (1 + s / (2 * Real.pi)) ≤ D * s := by
          have e : D * s = C' * s + C' * (s / Real.log 2) + C' * (s / (2 * Real.pi)) := by
            rw [hD]; ring
          have : C' ≤ C' * (s / Real.log 2) := le_mul_of_one_le_right hC'0 h1s
          have : 0 ≤ C' * s := mul_nonneg hC'0 hs0
          rw [e]; nlinarith
        have hM0 : 0 ≤ C' * (1 + s / (2 * Real.pi)) := by positivity
        calc (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ (g.factorial : ℝ) * (D * s) ^ g :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM g) (Nat.cast_nonneg _)
          _ = ((g.factorial : ℝ) * D ^ g) * s ^ g := by rw [mul_pow]; ring
          _ ≤ c * s ^ g := mul_le_mul_of_nonneg_right hcB (by positivity)
  refine ⟨hpd, fun i k => (hYv2.inv hu) i k, ?_⟩
  refine ⟨fun i j => ?_, ?_, fun k i j => ?_, fun k l i j => ?_, fun k l i j => ?_⟩
  · show ‖((imPeriod ha τ₀ B z).map Complex.ofReal)⁻¹ i j‖ ≤ _
    exact (GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef g (imPeriod ha τ₀ B z) c₀ hc₀ (h1 z hv) i j).trans hE.1
  · show ‖((Y z)⁻¹).det‖⁻¹ ≤ _
    rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_inv]
    have hT0 : 0 ≤ 1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)) := by
      have : 0 ≤ ∑ i : Fin a, tlog (z (Fin.castLE ha i)) :=
        Finset.sum_nonneg fun i _ => (tlog_pos (hv.2 i) (hz1.1 _)).le
      linarith
    have hPSD : (imPeriod ha τ₀ B z).PosSemidef := by
      have := (h1 z hv).add (PosSemidef.one.smul hc₀.le)
      simpa using this
    have hMPSD : ((C' * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ) -
        imPeriod ha τ₀ B z).PosSemidef := by
      have := (h2 z hv).add ((PosSemidef.one (n := Fin g) (R := ℝ)).smul
        (mul_nonneg (sub_nonneg.2 (le_max_left C 0)) hT0))
      convert this using 1
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hdet := GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow g (imPeriod ha τ₀ B z) _ (mul_nonneg hC'0 hT0) hPSD hMPSD
    refine hdet.trans ?_
    rw [hts]; exact hE.2
  · rw [hcG, Matrix.neg_apply, transpose_apply, norm_neg]
    exact (mul_le_mul_of_nonneg_right (hCe k j i) (hw0 k)).trans ((hKw k).trans hc5)
  · rw [hcurvG, Matrix.neg_apply, transpose_apply, norm_neg]
    have hP : ∀ p q, ‖(conn Yv v (coordVec l))ᵀᴴ p q‖ ≤ Kf l := fun p q => by
      rw [conjTranspose_apply, transpose_apply, norm_star]; exact hCe l p q
    have hprod := norm_mul_apply_le _ _ (Kf l) (Kf k) hP (hCe k) j i
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    calc ‖((conn Yv v (coordVec l))ᵀᴴ * conn Yv v (coordVec k)) j i‖ * (poinWt S v k * poinWt S v l)
        ≤ g * (Kf l * Kf k) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right hprod (mul_nonneg (hw0 k) (hw0 l))
      _ = g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) hg0
      _ ≤ 50 * g * C' ^ 2 := by nlinarith [sq_nonneg C']
      _ ≤ c := hc50
  · rw [hdelG, Matrix.neg_apply, transpose_apply, norm_neg, Matrix.sub_apply]
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    have hA := norm_mul_apply_le _ _ (Kf l) (Kf k) (hCe l) (hCe k) j i
    have hB := norm_mul_apply_le _ _ (Kf k) (Kf l) (hCe k) (hCe l) j i
    calc ‖(conn Yv v (coordVec l) * conn Yv v (coordVec k)) j i - (conn Yv v (coordVec k) * conn Yv v (coordVec l)) j i‖
          * (poinWt S v k * poinWt S v l)
        ≤ (g * (Kf l * Kf k) + g * (Kf k * Kf l)) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hA hB)) (mul_nonneg (hw0 k) (hw0 l))
      _ = 2 * g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ 2 * g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) (by positivity)
      _ = 50 * g * C' ^ 2 := by ring
      _ ≤ c := hc50

end GlobalTheory.HodgeInvGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  first | exact @GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | exact GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | (intros; apply GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumford
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumfordStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  exact @GlobalTheory.LieBaseGood.lieGram_isGood
end
