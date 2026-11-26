module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOne
open Matrix GlobalTheory.LKTrip

namespace GlobalTheory.HermitianMajorantIdentities

theorem mul_vecMulVec_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    A * vecMulVec u v * B = vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_vecMulVec {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec u (star u) *ᵥ x = (star x ⬝ᵥ u) * (star u ⬝ᵥ x) := by
  rw [vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]

theorem herm_swap {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ H *ᵥ x = star (star x ⬝ᵥ H *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]

end GlobalTheory.HermitianMajorantIdentities

namespace GlobalTheory


open GlobalTheory.HermitianMajorantIdentities in
theorem exists_posDef_majorant_of_sigPosH_eq_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  intro n H hH hdet hsig z hz
  set a : ℝ := (star z ⬝ᵥ H *ᵥ z).re with ha
  have hzz : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := by
    have h := herm_swap hH z z
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  set u : Fin n → ℂ := H *ᵥ z with hu
  have hux : ∀ x, star u ⬝ᵥ x = star z ⬝ᵥ H *ᵥ x := by
    intro x; rw [hu, star_mulVec, hH.eq, ← dotProduct_mulVec]
  refine ⟨((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hH.eq, conjTranspose_vecMulVec, star_star]
    simp [Complex.star_def]
  · intro x hx
    set q := star z ⬝ᵥ H *ᵥ x with hq
    set t : ℂ := q / (a : ℂ) with ht
    set x' := x - t • z with hx'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hzx' : star z ⬝ᵥ H *ᵥ x' = 0 := by
      rw [hx', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hzz, ← hq, ht, smul_eq_mul]
      field_simp; ring
    have hx'z : star x' ⬝ᵥ H *ᵥ z = 0 := by
      rw [herm_swap hH z x', hzx', star_zero]
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have hxe : x = t • z + x' := by rw [hx']; abel
    have hxx : star x ⬝ᵥ H *ᵥ x = star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x' := by
      conv_lhs => rw [hxe]
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzx', hx'z, hzz']
      ring
    have hxz : star x ⬝ᵥ H *ᵥ z = star q := herm_swap hH z x
    have hP : star x ⬝ᵥ (((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H) *ᵥ x
        = ((2 / a : ℝ) : ℂ) * (star q * q) - (star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x') := by
      rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, form_vecMulVec, hux, hxx,
        smul_eq_mul]
      rw [show star x ⬝ᵥ u = star q from hxz]
    have hqt : q = t * (a : ℂ) := by rw [ht]; field_simp
    have hnt : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hP, hqt, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e1 : ((starRingEnd ℂ) t * (a : ℂ) * (t * (a : ℂ))) = ((Complex.normSq t * a * a : ℝ) : ℂ) := by
      rw [← Complex.star_def, show star t * (a:ℂ) * (t * (a:ℂ)) = (star t * t) * ((a * a : ℝ) : ℂ) by push_cast; ring, hnt]
      push_cast; ring
    rw [e1, ← Complex.star_def, hnt]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul]
    have hapos : 0 < a := hz
    by_cases h0 : x' = 0
    · have htne : t ≠ 0 := by
        intro ht0
        apply hx
        rw [hxe, h0, ht0, zero_smul, add_zero]
      have hnpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr htne
      rw [h0]
      simp only [star_zero, zero_dotProduct, Complex.zero_re, add_zero]
      field_simp
      nlinarith [mul_pos hnpos hapos]
    · have hneg := re_form_neg_of_orth_of_sigPosH_eq_one H hH hdet hsig z x' hz hzx' h0
      have hn0 : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
      have : 2 / a * (Complex.normSq t * a * a) - Complex.normSq t * a = Complex.normSq t * a := by
        field_simp; ring
      nlinarith [mul_nonneg hn0 hapos.le]
  · intro Y s c hs hY hYz
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hA : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = (s : ℂ) * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hY,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hB : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = star c * (star z ⬝ᵥ H *ᵥ (Y *ᵥ x)) := by
      intro x
      rw [hYz, star_smul, smul_dotProduct, smul_eq_mul]
    have hsc : (s : ℂ) = star c * c := by
      have h1 := (hA z).symm.trans (hB z)
      rw [hYz, mulVec_smul, dotProduct_smul, smul_eq_mul, hzz'] at h1
      have h2 : ((s : ℂ) - star c * c) * (a : ℂ) = 0 := by rw [sub_mul, h1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha0)
    have hc0 : star c ≠ 0 := by
      intro h0
      have : (s : ℂ) = 0 := by rw [hsc, h0, zero_mul]
      exact hs.ne' (by exact_mod_cast this)
    have hrow : ∀ x, star z ⬝ᵥ H *ᵥ (Y *ᵥ x) = c * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      have h1 := (hA x).symm.trans (hB x)
      rw [hsc, mul_assoc] at h1
      exact (mul_left_cancel₀ hc0 h1).symm
    have hrowv : star u ᵥ* Y = c • star u := by
      funext j
      have h1 : (star u ᵥ* Y) ⬝ᵥ Pi.single j 1 = (c • star u) ⬝ᵥ Pi.single j 1 := by
        rw [← dotProduct_mulVec, hux, hrow, smul_dotProduct, hux, smul_eq_mul]
      simpa [dotProduct_single] using h1
    have hcolv : Yᴴ *ᵥ u = star c • u := by
      have h1 := congrArg star hrowv
      rw [star_vecMul, star_star, star_smul, star_star] at h1
      exact h1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hcolv,
      hrowv, hY]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hsc]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOneStatement
open Matrix GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  first | (exact @GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (exact GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (intros; apply GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBound
open Matrix

namespace GlobalTheory

theorem herm_scale_entry_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  intro n P _hP hpos
  cases n with
  | zero => exact ⟨0, fun _ _ _ _ i => i.elim0⟩
  | succ k =>
  set q : (Fin (k+1) → ℂ) → ℝ := fun x => (star x ⬝ᵥ P *ᵥ x).re with hq
  have hcont : Continuous q := by
    simp only [hq, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hsmul : ∀ (t : ℝ) (x : Fin (k+1) → ℂ), q ((t : ℂ) • x) = t ^ 2 * q x := by
    intro t x
    simp only [hq, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  obtain ⟨x0, hx0S, hmin⟩ := (isCompact_sphere (0 : Fin (k+1) → ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  set m := q x0 with hm_def
  have hx0 : x0 ≠ 0 := by
    intro h; rw [h] at hx0S; simp at hx0S
  have hm : 0 < m := hpos x0 hx0
  have hlow : ∀ x, m * ‖x‖ ^ 2 ≤ q x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hq]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : Fin (k+1) → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
    have huS : u ∈ Metric.sphere (0 : Fin (k+1) → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hxu : x = ((‖x‖ : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
    have h1 : m ≤ q u := hmin huS
    have hqx : q x = ‖x‖ ^ 2 * q u := by
      conv_lhs => rw [hxu]
      exact hsmul _ _
    rw [hqx]
    nlinarith [sq_nonneg ‖x‖]
  have hY : ∀ (Y : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (s : ℝ), Yᴴ * P * Y = (s : ℂ) • P →
      ∀ x, q (Y *ᵥ x) = s * q x := by
    intro Y s h x
    simp only [hq]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  set C : ℝ := ∑ j, ‖P j j‖ with hC
  refine ⟨C / m, fun Y s hs h i j => ?_⟩
  set e : Fin (k+1) → ℂ := Pi.single j 1 with he
  have hYe : Y *ᵥ e = fun i => Y i j := by
    rw [he, mulVec_single_one]; rfl
  have hqe : q e = (P j j).re := by
    simp [hq, he, mulVec_single_one]
  have hle : ‖Y i j‖ ≤ ‖Y *ᵥ e‖ := by
    rw [hYe]; exact norm_le_pi_norm (fun i => Y i j) i
  have hPjj : (P j j).re ≤ C :=
    (Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun j => ‖P j j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have key : m * ‖Y *ᵥ e‖ ^ 2 ≤ s * (P j j).re := by
    rw [← hqe, ← hY Y s h e]; exact hlow _
  have h2 : ‖Y i j‖ ^ 2 ≤ ‖Y *ᵥ e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hPjj hs.le]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBoundStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_similitude_entry_sq_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  first | (exact @GlobalTheory.herm_scale_entry_bound) | (exact GlobalTheory.herm_scale_entry_bound) | (intros; apply GlobalTheory.herm_scale_entry_bound  <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ArchBound

theorem entries_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P →
      ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s :=
  GlobalTheory.T.hermitian_similitude_entry_sq_bound

theorem majorant : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 →
    ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H →
        Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P :=
  GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one

variable {p : ℕ} [Fact p.Prime]

theorem sh_inv_mul (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
  set u : G.Cˣ := (y : G.Cˣ × ℚˣ).1
  set s : ℚ := (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have h : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β := y.2.1
  have h1 : sh G u = algebraMap ℚ G.C s * (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * β) := by
    calc sh G u = (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C)) * ((u : G.C) * β * sh G u) := by
          simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [h]; simp only [← Algebra.smul_def, mul_smul_comm, mul_assoc]
  rw [h1]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_assoc, Units.mul_inv_cancel_left]
  rw [Units.inv_mul, mul_one]

theorem psi_algebraMap (G : HTGroup p) (w : InfinitePlace G.F) (q : ℚ) :
    G.psi w (algebraMap ℚ G.C q) = ((q : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have := ((G.psi w).toRatAlgHom).commutes q
  simp only [RingHom.toRatAlgHom_apply] at this
  rw [this, Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, Rat.smul_def]

theorem herm_sim (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : InfinitePlace G.F) :
    (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * herm G w β * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • herm G w β := by
  have h := congrArg (G.psi w) (sh_inv_mul G β y)
  rw [map_mul, map_mul, map_mul, psi_algebraMap] at h
  have hs : G.psi w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
      (G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w := G.psi_star w _
  rw [hs] at h
  have hg : IsUnit (G.gram w).det := isUnit_iff_ne_zero.2 (G.gram_det w)
  unfold herm
  calc _ = G.gram w * ((G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w *
        G.psi w ((β⁻¹ : G.Cˣ) : G.C) * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    _ = _ := by rw [h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem herm_congr (G : HTGroup p) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (v : InfinitePlace G.F) :
    ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.ArchBound

namespace GlobalTheory.ArchBound

variable {p : ℕ} [Fact p.Prime]

theorem sigPosH_eq_zero_of_ne (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (w : InfinitePlace G.F) (hw : w ≠ v) : sigPosH (G.gram_herm w) = 0 := by
  rcases G.sig w with ⟨h1, -⟩ | ⟨h0, -⟩
  · exfalso
    have hc : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} = 1 := ha
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hc
    have e1 := hx ⟨v, hv⟩
    have e2 := hx ⟨w, h1⟩
    exact hw (by rw [← e2] at e1; exact (congrArg Subtype.val e1).symm)
  · exact h0

theorem exists_majorant (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) (w : InfinitePlace G.F) :
    ∃ P : Matrix (Fin G.n) (Fin G.n) ℂ, P.IsHermitian ∧
      (∀ x : Fin G.n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ y : grp G β, FixL G v β y z →
        (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * P * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
          (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • P := by
  obtain ⟨Z, hZ⟩ := herm_congr G β hR w
  have hH : (herm G w β).IsHermitian := by
    rw [hZ]; unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (G.gram_herm w).eq, Matrix.mul_assoc]
  have hdet : (herm G w β).det ≠ 0 := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hz0 : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnits_det_units Z).ne_zero
    exact mul_ne_zero (mul_ne_zero (by simpa using hz0) (G.gram_det w)) hz0
  have hsig : sigPosH hH = sigPosH (G.gram_herm w) :=
    GlobalTheory.SigCong.sigPosH_congr (G.gram w) (G.gram_herm w) (G.gram_det w) Z _ hH hZ
  by_cases hw : w = v
  · subst hw
    obtain ⟨P, hPh, hPp, hPs⟩ := majorant (herm G w β) hH hdet (hsig.trans hv) z hz
    refine ⟨P, hPh, hPp, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hy
    exact hPs _ _ c (by exact_mod_cast y.2.2) (herm_sim G β y w) hc
  · have h0 := sigPosH_eq_zero_of_ne G ha v hv w hw
    refine ⟨-herm G w β, hH.neg, fun x hx => ?_, fun y _ => ?_⟩
    · have := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (herm G w β) hH hdet (hsig.trans h0) x hx
      rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
      linarith
    · rw [Matrix.mul_neg, Matrix.neg_mul, herm_sim G β y w, smul_neg]

end GlobalTheory.ArchBound


open GlobalTheory.ArchBound in
theorem GlobalTheory.LKCx.entries_sq_le_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re →
    ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n),
      ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  intro p _ G ha v hv β _ hR z hz
  choose P hPh hPp hPs using exists_majorant G ha v hv β hR z hz
  choose K hK using fun w => entries_bound (P w) (hPh w) (hPp w)
  refine ⟨∑ w, |K w|, fun y hy w i j => ?_⟩
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  refine (hK w _ _ hs (hPs w y hy) i j).trans ?_
  refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) hs.le
  exact Finset.single_le_sum (f := fun w => |K w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
