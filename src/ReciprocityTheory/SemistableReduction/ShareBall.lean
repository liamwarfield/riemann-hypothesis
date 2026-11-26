module

public import ReciprocityTheory.SemistableReduction.ShareBallA

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.ShareBallC
section -- merged from ReciprocityTheory.SemistableReduction.ShareBallB
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

def sbDp (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 1 else 0

def sbDn (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 0 else 1

theorem sb_signMat_eq (p r : ℕ) : signMat p r = sbDp p r - sbDn p r := by
  simp only [signMat, sgn, sbDp, sbDn, diagonal_sub]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_add_Dn (p r : ℕ) : sbDp p r + sbDn p r = 1 := by
  simp only [sbDp, sbDn, diagonal_add]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dp (p r : ℕ) : sbDp p r * sbDp p r = sbDp p r := by
  simp only [sbDp, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dn (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by
  simp only [sbDn, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dn (p r : ℕ) : sbDp p r * sbDn p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dp (p r : ℕ) : sbDn p r * sbDp p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_herm (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by
  simp only [sbDp, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_Dn_herm (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by
  simp only [sbDn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_herm (p r : ℕ) : (signMat p r)ᴴ = signMat p r := by
  simp only [signMat, sgn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_mul_J (p r : ℕ) : signMat p r * signMat p r = 1 := by
  simp only [signMat, sgn, diagonal_mul_diagonal]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = normSq (sbDp p r *ᵥ u) := by
  simp only [posSq, normSq, sbDp, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by
  simp only [negSq, normSq, sbDn, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_herm_swap {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [star_mulVec, hM, dotProduct_mulVec]

theorem sb_dot_Dp (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dp_herm p r) v (sbDp p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dp_mul_Dp] at h
  exact h

theorem sb_dot_Dn (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dn_herm p r) v (sbDn p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dn_mul_Dn] at h
  exact h

theorem sb_dot_split (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [← sb_dot_Dp p v w, ← sb_dot_Dn p v w, ← dotProduct_add, ← add_mulVec, sb_Dp_add_Dn,
    one_mulVec]

theorem sb_dot_J (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [sb_signMat_eq, sub_mulVec, dotProduct_sub, sb_dot_Dp p v w, sb_dot_Dn p v w]

private theorem re_star_dotProduct_self_eq_normSq {r : ℕ} (x : Fin r → ℂ) : (star x ⬝ᵥ x).re = normSq x := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, normSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (star (x k) * x k).re = (x k).re * (x k).re + (x k).im * (x k).im := by
    simp [Complex.mul_re] <;> ring
  rw [h1, ← Complex.normSq_apply]
  first
    | exact (Complex.sq_norm _).symm
    | exact Complex.normSq_eq_norm_sq _
    | simp [Complex.sq_abs]

theorem sb_re_dot_J (p : ℕ) {r : ℕ} (v : Fin r → ℂ) :
    (star v ⬝ᵥ (signMat p r *ᵥ v)).re = posSq p v - negSq p v := by
  rw [sb_dot_J, Complex.sub_re, re_star_dotProduct_self_eq_normSq, re_star_dotProduct_self_eq_normSq, sb_posSq_eq, sb_negSq_eq]

theorem sb_cs {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re ^ 2 ≤ normSq v * normSq w := by
  have h1 : |(star v ⬝ᵥ w).re| ≤ ∑ k, ‖v k‖ * ‖w k‖ := by
    have e1 : |(star v ⬝ᵥ w).re| ≤ ‖star v ⬝ᵥ w‖ := by
      first
        | exact Complex.abs_re_le_norm _
        | exact RCLike.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
    have e2 : ‖star v ⬝ᵥ w‖ ≤ ∑ k, ‖star (v k) * w k‖ := by
      unfold dotProduct
      exact norm_sum_le _ _
    have e3 : ∑ k, ‖star (v k) * w k‖ = ∑ k, ‖v k‖ * ‖w k‖ := by
      simp [norm_mul, norm_star]
    linarith
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖) (fun k => ‖w k‖)
  have h3 : (star v ⬝ᵥ w).re ^ 2 ≤ (∑ k, ‖v k‖ * ‖w k‖) ^ 2 :=
    sq_le_sq.mpr (h1.trans (le_abs_self _))
  unfold normSq
  exact h3.trans h2

private theorem two_mul_one_add_mul_le_of_le_mul (a b c d s : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hcd : c ≤ s * d) (hs1 : s < 1) (hle : a * c ≤ b * d) :
    2 * (1 + s) * (a * c) ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
  rcases eq_or_lt_of_le hd with h0 | hdpos
  · subst h0
    have hc0 : c = 0 := le_antisymm (by simpa using hcd) hc
    subst hc0
    nlinarith [mul_nonneg hs (sq_nonneg a), sq_nonneg b]
  · have hsq : (a * c) * (a * c) ≤ (b * d) * (b * d) :=
      mul_self_le_mul_self (mul_nonneg ha hc) hle
    have hdc : 0 ≤ d - c := by nlinarith
    have hsdc : 0 ≤ s * d - c := by linarith
    have e1 : 0 ≤ (s * d ^ 2 + c ^ 2) * (a - d) ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg hs (sq_nonneg d)) (sq_nonneg c)) (sq_nonneg _)
    have e2 : 0 ≤ 2 * a * d * ((d - c) * (s * d - c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha) hd) (mul_nonneg hdc hsdc)
    have hd2 : 0 < d ^ 2 := pow_pos hdpos 2
    by_contra hneg
    push_neg at hneg
    have e3 := mul_lt_mul_of_pos_left hneg hd2
    nlinarith

theorem sb_real_bounds (a b c d s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hs1 : s < 1) (hba : b ≤ s * a) (hcd : c ≤ s * d) (h1 : |t| ≤ a * c)
    (h2 : |t| ≤ b * d) :
    0 ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 + 2 * (1 + s) * t ∧
      0 ≤ s * (a ^ 2 + d ^ 2) - (b ^ 2 + c ^ 2) - 2 * (1 - s) * t := by
  have hTc : |t| ≤ a * c := h1
  have hTad : |t| ≤ s * a * d := by
    have := mul_le_mul_of_nonneg_left hcd ha
    nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith
  have key : 2 * (1 + s) * |t| ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
    rcases le_total (a * c) (b * d) with hle | hle
    · have e := two_mul_one_add_mul_le_of_le_mul a b c d s ha hc hd hs hcd hs1 hle
      have e' := mul_le_mul_of_nonneg_left hTc (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
    · have e := two_mul_one_add_mul_le_of_le_mul d c b a s hd hb ha hs hba hs1
        (by rw [mul_comm d b, mul_comm c a]; exact hle)
      have e' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
  have htl : 0 ≤ t + |t| := by linarith [neg_abs_le t]
  have htu : t ≤ |t| := le_abs_self t
  have hb2 : b * b ≤ (s * a) * (s * a) := mul_self_le_mul_self hb hba
  have hc2 : c * c ≤ (s * d) * (s * d) := mul_self_le_mul_self hc hcd
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)) htl]
  · nlinarith [mul_nonneg (mul_nonneg hs hs0) (sq_nonneg (a - d)),
      mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s * a * d - t)]

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Module
open scoped ComplexOrder

theorem sb_re_dot_comm {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re = (star w ⬝ᵥ v).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sb_normSq_split (p : ℕ) {r : ℕ} (v : Fin r → ℂ) : normSq v = posSq p v + negSq p v := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_normSq_nonneg {r : ℕ} (v : Fin r → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sb_setup {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r)
    (hP : ∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) :
    ∀ w : Fin r → ℂ, ∃ x, signMat p r *ᵥ (H *ᵥ x) = x ∧ sbDp p r *ᵥ x = sbDp p r *ᵥ w := by
  intro w
  have hJJ : signMat p r * signMat p r = 1 := sb_J_mul_J p r
  have hA2 : signMat p r * H * (signMat p r * H) = 1 := by
    calc signMat p r * H * (signMat p r * H) = signMat p r * (H * signMat p r * H) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have hHx : ∀ x : Fin r → ℂ, H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
    intro x; rw [mulVec_mulVec, hJJ, one_mulVec]
  have hre : ∀ x : Fin r → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx
    have := hH.re_dotProduct_pos hx
    simpa using this
  have hplus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = x → sbDp p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, sb_re_dot_J, sb_posSq_eq, hDx, sb_negSq_eq] at h1
    have h2 := sb_normSq_nonneg (sbDn p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  have hminus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = -x → sbDn p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, mulVec_neg, dotProduct_neg, Complex.neg_re, sb_re_dot_J, sb_posSq_eq,
      sb_negSq_eq, hDx] at h1
    have h2 := sb_normSq_nonneg (sbDp p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin r) ℂ, P = (1 / 2 : ℂ) • (1 + signMat p r * H) :=
    ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin r) (Fin r) ℂ, N = (1 / 2 : ℂ) • (1 - signMat p r * H) :=
    ⟨_, rfl⟩
  have hAP : signMat p r * H * P = P := by
    rw [hP, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hA2, add_comm]
  have hAN : signMat p r * H * N = -N := by
    rw [hN, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hA2, ← smul_neg, neg_sub]
  have hPN : P + N = 1 := by
    rw [hP, hN]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPv : ∀ x, signMat p r *ᵥ (H *ᵥ (P *ᵥ x)) = P *ᵥ x := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAP]
  have hNv : ∀ x, signMat p r *ᵥ (H *ᵥ (N *ᵥ x)) = -(N *ᵥ x) := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAN, neg_mulVec]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin r) (Fin r) ℂ, F = sbDp p r * P + sbDn p r * N := ⟨_, rfl⟩
  have hFp : ∀ x, sbDp p r *ᵥ (F *ᵥ x) = sbDp p r *ᵥ (P *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dp_mul_Dp,
      sb_Dp_mul_Dn, zero_mul, zero_mulVec, add_zero]
  have hFn : ∀ x, sbDn p r *ᵥ (F *ᵥ x) = sbDn p r *ᵥ (N *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dn_mul_Dn,
      sb_Dn_mul_Dp, zero_mul, zero_mulVec, zero_add]
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    have h0 : F *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
    have hp : P *ᵥ (x - y) = 0 := hplus _ (hPv _) (by rw [← hFp, h0, mulVec_zero])
    have hn : N *ᵥ (x - y) = 0 := hminus _ (hNv _) (by rw [← hFn, h0, mulVec_zero])
    have : x - y = 0 := by
      rw [← one_mulVec (x - y), ← hPN, add_mulVec, hp, hn, add_zero]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective F.mulVec :=
    mulVec_surjective_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨x, hx⟩ := hsurj (sbDp p r *ᵥ w)
  refine ⟨P *ᵥ x, hPv x, ?_⟩
  rw [← hFp, hx, mulVec_mulVec, sb_Dp_mul_Dp]

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

theorem boundedBall_holds : BoundedBallStatement := by
  intro r p H s hH hJ hs0 hs1 hP u
  have hHh : Hᴴ = H := hH.isHermitian
  have hsurj := sb_setup hH hJ hP
  have hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]
  have hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x := fun x hx => by
    calc H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hx]
  have hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y) := fun y hy => by
    calc H *ᵥ y = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ y)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hy, mulVec_neg]
  have horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star x ⬝ᵥ (signMat p r *ᵥ y) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh x y
    rw [hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (-1 / 2 : ℂ) * e
  have horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star y ⬝ᵥ (signMat p r *ᵥ x) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh y x
    rw [hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (1 / 2 : ℂ) * e
  have hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero, hxy] at o
    have hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re := by
      rw [← o, sb_re_star_dot, sb_posSq_eq]
    have cs := sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)
    rw [← hA, ← sb_negSq_eq, ← sb_negSq_eq] at cs
    have hx' := hP x hx
    have hpx : posSq p x = posSq p y := by rw [sb_posSq_eq, sb_posSq_eq, hxy]
    have hA0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
    have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
    rw [hpx] at hx'
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have h2 := mul_le_mul_of_nonneg_right hx' hD0
      exact le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤
        posSq p y * (s ^ 2 * negSq p y)) h
  have hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u :=
    ⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)),
      by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm],
      by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub],
      by ext k; simp; ring⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := hdec
  have hPx := hP x hx
  have hPy := hNprop y hy
  set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef
  have ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t := by
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero] at o
    rw [htdef, o]
  have hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y := by
    have e1 := sb_re_dot_J p x
    have e2 := sb_re_dot_J p y
    rw [hq, mulVec_add, hHx x hx, hHy y hy, star_add]
    simp only [add_dotProduct, dotProduct_add, dotProduct_neg]
    rw [horth x y hx hy, horth' x y hx hy]
    simp only [Complex.add_re, Complex.neg_re, Complex.zero_re]
    linarith
  have hn_eq : normSq (x + y) =
      posSq p x + negSq p x + posSq p y + negSq p y + 4 * t := by
    have a3 : (star x ⬝ᵥ y).re = 2 * t := by rw [sb_dot_split p, Complex.add_re, ht2]; ring
    have a4 : (star y ⬝ᵥ x).re = 2 * t := by rw [sb_re_dot_comm, a3]
    rw [← sb_re_star_dot, star_add]
    simp only [add_dotProduct, dotProduct_add, Complex.add_re]
    rw [a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]
    ring
  have hA0 : 0 ≤ posSq p x := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hB0 : 0 ≤ negSq p x := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hC0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hts1 : t ^ 2 ≤ posSq p x * posSq p y := by
    rw [sb_posSq_eq, sb_posSq_eq]; exact sb_cs _ _
  have hts2 : t ^ 2 ≤ negSq p x * negSq p y := by
    rw [← ht2, sb_negSq_eq, sb_negSq_eq]; exact sb_cs _ _
  have hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z := fun z hz => by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
  have hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x) :=
    (Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))
  have hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y) :=
    (Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))
  have h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y) := by
    rw [← Real.sqrt_mul hA0]; exact Real.abs_le_sqrt hts1
  have h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y) := by
    rw [← Real.sqrt_mul hB0]; exact Real.abs_le_sqrt hts2
  obtain ⟨hU, hL⟩ := sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0] at hU hL
  have h1s : 0 < 1 - s := by linarith
  rw [hq_eq, hn_eq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith

end ReciprocityTheory.MultiplicativeHeights
