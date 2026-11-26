module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

structure Bs (A k b sb PP TO rd : ℝ) : Prop where
  forty_eight_le_constant : 48 ≤ A
  k8 : 8 ≤ k
  Ak : A ≤ 2 * k ^ 2
  sb_sq : sb * sb = b
  PPA : 10 ^ 60 * A ≤ PP
  h32 : PP ^ 3 * TO ^ 2 ≤ sb
  hTP : TO * PP ≤ sb
  one_le_order_alt : 1 ≤ TO
  rd1 : 1 ≤ rd
  rd8 : rd ^ 8 ≤ sb

namespace Bs

variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h

theorem PP_ge : (10 : ℝ) ^ 60 ≤ PP := by
  have h1 := h.PPA
  have h2 := h.forty_eight_le_constant
  linarith

theorem large_constant_le_param_cube : 10 ^ 100 * A ^ 2 ≤ PP ^ 3 := by
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ 10 ^ 60 * A := by linarith
  have h1 : (10 ^ 60 * A) ^ 3 ≤ PP ^ 3 := pow_le_pow_left₀ hA0 h.PPA 3
  have h2 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA1 (by norm_num)
  have h3 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have h4 : (10 ^ 60 * A) ^ 3 = 10 ^ 180 * A ^ 3 := by ring
  rw [h4] at h1
  linarith

theorem ATO : 10 ^ 100 * (A ^ 2 * TO ^ 2) ≤ sb := by
  have h1 : 10 ^ 100 * A ^ 2 * TO ^ 2 ≤ PP ^ 3 * TO ^ 2 :=
    mul_le_mul_of_nonneg_right h.large_constant_le_param_cube (sq_nonneg TO)
  calc 10 ^ 100 * (A ^ 2 * TO ^ 2) = 10 ^ 100 * A ^ 2 * TO ^ 2 := by ring
    _ ≤ PP ^ 3 * TO ^ 2 := h1
    _ ≤ sb := h.h32

theorem sb_ge : (10 : ℝ) ^ 100 ≤ sb := by
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hT1 := h.one_le_order_alt
  have hAT : (1 : ℝ) ≤ A * TO := by nlinarith
  have hQ : (1 : ℝ) ≤ A ^ 2 * TO ^ 2 := by nlinarith
  have := h.ATO
  nlinarith

theorem sb_le_b : sb ≤ b := by
  have h1 := h.sb_ge
  rw [← h.sb_sq]
  nlinarith

theorem b_ge : (10 : ℝ) ^ 100 ≤ b := le_trans h.sb_ge h.sb_le_b

theorem ATOb : 10 ^ 100 * (A ^ 2 * TO ^ 2) ≤ b := le_trans h.ATO h.sb_le_b

theorem TO_le_sb : TO ≤ sb := by
  have hP : (1 : ℝ) ≤ PP := le_trans (by norm_num) h.PP_ge
  have h1 : TO * 1 ≤ TO * PP := mul_le_mul_of_nonneg_left hP (by linarith [h.one_le_order_alt])
  linarith [h.hTP]

theorem PP_le_sb : PP ≤ sb := by
  have hP : (0 : ℝ) ≤ PP := le_trans (by norm_num) h.PP_ge
  have h1 : PP * 1 ≤ PP * TO := mul_le_mul_of_nonneg_left h.one_le_order_alt hP
  linarith [h.hTP]

theorem param_cube_le_bound : PP ^ 3 ≤ sb := by
  have hP : (0 : ℝ) ≤ PP := le_trans (by norm_num) h.PP_ge
  have hT : (1 : ℝ) ≤ TO ^ 2 := by nlinarith [h.one_le_order_alt]
  have h1 : PP ^ 3 * 1 ≤ PP ^ 3 * TO ^ 2 := mul_le_mul_of_nonneg_left hT (pow_nonneg hP 3)
  linarith [h.h32]

theorem rd_pow_le {n : ℕ} (hn : n ≤ 8) : rd ^ n ≤ sb :=
  le_trans (pow_le_pow_right₀ h.rd1 hn) h.rd8

end Bs

structure Rn (A k b sb PP TO rd r D2 nW nP q0 : ℝ) : Prop extends Bs A k b sb PP TO rd where
  r6 : 6 ≤ r
  rA : 8 * r ≤ A
  two_le_degree_alt : 2 ≤ D2
  W : D2 * nW + 2 * r ≤ TO
  forty_mul_degree_le_order : 40 * D2 ≤ TO
  forty_le_weight_count : 40 ≤ nW
  projectivePointSizes : 0 ≤ nP
  nPW : nP ≤ nW
  q0lo : b ≤ TO * q0
  q0hi : TO * q0 ≤ b + TO

namespace Rn

variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h

theorem nW_le : nW ≤ TO := by
  have h1 : 2 * nW ≤ D2 * nW := mul_le_mul_of_nonneg_right h.two_le_degree_alt (by linarith [h.forty_le_weight_count])
  linarith [h.W, h.r6, h.forty_le_weight_count]

theorem modulus_pos_alt : 0 < q0 := by
  have hb := h.toBs.b_ge
  have h1 := h.q0lo
  have h2 := h.one_le_order_alt
  nlinarith

theorem TO_le_sq : TO ≤ TO ^ 2 := by
  have h1 : TO * 1 ≤ TO * TO := mul_le_mul_of_nonneg_left h.one_le_order_alt (by linarith [h.one_le_order_alt])
  nlinarith

theorem kl_le : D2 * nW + 2 * r + (TO + D2) * q0 ≤ 3 * TO + 2 * b := by
  have hq := h.modulus_pos_alt
  have h40 : 40 * D2 * q0 ≤ TO * q0 := mul_le_mul_of_nonneg_right h.forty_mul_degree_le_order hq.le
  have hb : (0 : ℝ) ≤ b := le_trans (by norm_num) h.toBs.b_ge
  linarith [h.W, h.q0hi, h.one_le_order_alt]

theorem TQ_le : (TO + D2) * (TO + D2 + 2 * r) ≤ 6 * TO ^ 2 := by
  have hT1 := h.one_le_order_alt
  have hD2 := h.two_le_degree_alt
  have hr6 := h.r6
  have hDW : D2 * 1 ≤ D2 * nW := mul_le_mul_of_nonneg_left (by linarith [h.forty_le_weight_count]) (by linarith)
  have hQ : TO + D2 + 2 * r ≤ 3 * TO := by linarith [h.W, h.forty_mul_degree_le_order]
  have hD : TO + D2 ≤ 2 * TO := by linarith [h.forty_mul_degree_le_order]
  calc (TO + D2) * (TO + D2 + 2 * r) ≤ (2 * TO) * (3 * TO) :=
        mul_le_mul hD hQ (by linarith) (by linarith)
    _ = 6 * TO ^ 2 := by ring

theorem Q_le : TO + D2 + 2 * r ≤ 3 * TO := by
  have h1 : 0 ≤ D2 * nW := mul_nonneg (by linarith [h.two_le_degree_alt]) (by linarith [h.forty_le_weight_count])
  linarith [h.forty_mul_degree_le_order, h.W, h.one_le_order_alt]

theorem sq_mul_sq_le : A ^ 2 * TO ^ 2 ≤ b := by
  have h1 := h.toBs.ATOb
  have h2 : 0 ≤ A ^ 2 * TO ^ 2 := by positivity
  linarith

theorem b_le_Ab : b ≤ A * b := by
  have hb : (0 : ℝ) ≤ b := le_trans (by norm_num) h.toBs.b_ge
  have h1 : b * 1 ≤ b * A := mul_le_mul_of_nonneg_left (by linarith [h.forty_eight_le_constant]) hb
  linarith

theorem sK {s : ℝ} (hs : s ≤ A * (D2 * nW + 2 * r + (TO + D2) * q0 + r * ((TO + D2) * (TO + D2 + 2 * r))) +
    A * (nP + TO * nW) + 1) : s ≤ 4 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hkl := h.kl_le
  have hTQ := h.TQ_le
  have hY0 : 0 ≤ (TO + D2) * (TO + D2 + 2 * r) := mul_nonneg (by linarith) (by linarith)
  have e1 : r * ((TO + D2) * (TO + D2 + 2 * r)) ≤ A * (6 * TO ^ 2) :=
    mul_le_mul hrA hTQ hY0 hA0
  have hnW := h.nW_le
  have hnP : nP ≤ TO := le_trans h.nPW hnW
  have e2 : TO * nW ≤ TO * TO := mul_le_mul_of_nonneg_left hnW hT0
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hTA : TO ≤ A * TO := le_mul_of_one_le_left hT0 hA1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have p2 : A * TO * TO ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have hB := h.toBs.ATOb
  have hBA := h.b_le_Ab
  have i1 : A * (D2 * nW + 2 * r + (TO + D2) * q0 + r * ((TO + D2) * (TO + D2 + 2 * r))) ≤
      A * (3 * TO + 2 * b + A * (6 * TO ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) hA0
  have i2 : A * (nP + TO * nW) ≤ A * (TO + TO * TO) := mul_le_mul_of_nonneg_left (by linarith) hA0
  have f1 : A * (3 * TO + 2 * b + A * (6 * TO ^ 2)) = 2 * (A * b) + 3 * (A * TO) + 6 * (A ^ 2 * TO ^ 2) := by ring
  have f2 : A * (TO + TO * TO) = A * TO + A * TO * TO := by ring
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have f3 : A * b = A * b := rfl
  have hAb : b ≤ A * b := hBA
  nlinarith

theorem sL {s : ℝ} (hs : s ≤ A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) : s * TO ≤ 2 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hQ := h.Q_le
  have hnW := h.nW_le
  have hq := h.q0hi
  have hX : s * TO ≤ (A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) * TO :=
    mul_le_mul_of_nonneg_right hs hT0
  have e1 : r * (TO + D2 + 2 * r) ≤ A * (3 * TO) := mul_le_mul hrA hQ (by linarith) hA0
  have e2 : r * (TO + D2 + 2 * r) * TO ≤ A * (3 * TO) * TO := mul_le_mul_of_nonneg_right e1 hT0
  have e3 : nW * TO ≤ TO * TO := mul_le_mul_of_nonneg_right hnW hT0
  have e4 : A * (TO * q0) ≤ A * (b + TO) := mul_le_mul_of_nonneg_left hq hA0
  have e5 : A * (r * (TO + D2 + 2 * r) * TO) ≤ A * (A * (3 * TO) * TO) := mul_le_mul_of_nonneg_left e2 hA0
  have e6 : A * (nW * TO) ≤ A * (TO * TO) := mul_le_mul_of_nonneg_left e3 hA0
  have eX : (A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) * TO =
      A * (TO * q0) + A * (r * (TO + D2 + 2 * r) * TO) + A * (nW * TO) + TO := by ring
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hTA : TO ≤ A * TO := le_mul_of_one_le_left hT0 hA1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have p2 : A * TO * TO ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have eA : A * (A * (3 * TO) * TO) = 3 * (A * TO * (A * TO)) := by ring
  have eB : A * (TO * TO) = A * TO * TO := by ring
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have eC : A * (b + TO) = A * b + A * TO := by ring
  have hB := h.toBs.ATOb
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have hAb := h.b_le_Ab
  linarith

theorem dL {d : ℝ} (hd : d ≤ A * (q0 + r * (TO + D2 + 2 * r))) : d ≤ 2 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hQ := h.Q_le
  have hq0 := h.modulus_pos_alt
  have hq1 : q0 * 1 ≤ q0 * TO := mul_le_mul_of_nonneg_left hT1 hq0.le
  have hq : q0 ≤ b + TO := by linarith [h.q0hi]
  have e1 : r * (TO + D2 + 2 * r) ≤ A * (3 * TO) := mul_le_mul hrA hQ (by linarith) hA0
  have e2 : A * (q0 + r * (TO + D2 + 2 * r)) ≤ A * (b + TO + A * (3 * TO)) :=
    mul_le_mul_of_nonneg_left (by linarith) hA0
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have hTT : A * A * TO ≤ A * A * (TO * TO) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have eA : A * (b + TO + A * (3 * TO)) = A * b + A * TO + 3 * (A * A * TO) := by ring
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have eQ : A * A * (TO * TO) = A ^ 2 * TO ^ 2 := by ring
  have hB := h.toBs.ATOb
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have hAb := h.b_le_Ab
  linarith

end Rn

theorem absorb {k b c : ℝ} (hk : 1 ≤ k) (hb : 10 ^ 100 ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ 10 ^ 100) {i j : ℕ} (hi : i ≤ 8)
    (hj : j + 1 ≤ 8) : c * k ^ i * b ^ j ≤ (k * b) ^ 8 := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) hb
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hki : k ^ i ≤ k ^ 8 := pow_le_pow_right₀ hk hi
  have hbj : b ^ j ≤ b ^ 7 := pow_le_pow_right₀ hb1 (by omega)
  have s1 : c * k ^ i ≤ 10 ^ 100 * k ^ 8 := mul_le_mul hc hki (pow_nonneg hk0 i) (by norm_num)
  have s2 : c * k ^ i * b ^ j ≤ 10 ^ 100 * k ^ 8 * b ^ 7 :=
    mul_le_mul s1 hbj (pow_nonneg hb0 j) (mul_nonneg (by norm_num) (pow_nonneg hk0 8))
  have s3 : 10 ^ 100 * k ^ 8 * b ^ 7 ≤ b * k ^ 8 * b ^ 7 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (pow_nonneg hk0 8)) (pow_nonneg hb0 7)
  calc c * k ^ i * b ^ j ≤ b * k ^ 8 * b ^ 7 := le_trans s2 s3
    _ = (k * b) ^ 8 := by ring

namespace Rn

variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h

theorem b_pos : 0 < b := lt_of_lt_of_le (by norm_num) h.toBs.b_ge

theorem sb_pos : 0 < sb := lt_of_lt_of_le (by norm_num) h.toBs.sb_ge

theorem PP_pos : 0 < PP := lt_of_lt_of_le (by norm_num) h.toBs.PP_ge

theorem d_le {d : ℝ} (hd : d ≤ 2 * A * b) : d ≤ 4 * k ^ 2 * b := by
  have h1 : A * b ≤ 2 * k ^ 2 * b := mul_le_mul_of_nonneg_right h.Ak h.b_pos.le
  linarith

theorem d_sq {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) : d ^ 2 ≤ 16 * k ^ 4 * b ^ 2 := by
  have h1 := pow_le_pow_left₀ hd0 (h.d_le hd) 2
  calc d ^ 2 ≤ (4 * k ^ 2 * b) ^ 2 := h1
    _ = 16 * k ^ 4 * b ^ 2 := by ring

theorem k1 : 1 ≤ k := by linarith [h.k8]

theorem h3a {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) :
    (rd ^ 2) ^ 4 * PP ^ 3 * d ^ 2 ≤ q := by
  have hsb0 := h.sb_pos.le
  have e1 : (rd ^ 2) ^ 4 ≤ sb := by
    have : (rd ^ 2) ^ 4 = rd ^ 8 := by ring
    rw [this]; exact h.rd8
  have e2 : PP ^ 3 ≤ sb := h.toBs.param_cube_le_bound
  have e3 := h.d_sq hd0 hd
  have s1 : (rd ^ 2) ^ 4 * PP ^ 3 ≤ sb * sb := mul_le_mul e1 e2 (pow_nonneg h.PP_pos.le 3) hsb0
  have s2 : (rd ^ 2) ^ 4 * PP ^ 3 * d ^ 2 ≤ sb * sb * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul s1 e3 (sq_nonneg d) (mul_nonneg hsb0 hsb0)
  have s3 : sb * sb * (16 * k ^ 4 * b ^ 2) = 16 * k ^ 4 * b ^ 3 := by
    rw [h.sb_sq]; ring
  have s4 : 16 * k ^ 4 * b ^ 3 ≤ (k * b) ^ 8 :=
    absorb h.k1 h.toBs.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem r_le : r ≤ k ^ 2 := by linarith [sq_nonneg k, h.rA, h.Ak]

theorem h3b {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) :
    TO * (1250 * r) * rd ^ 2 * PP * d ^ 2 ≤ q := by
  have B := h.toBs
  have hb0 := h.b_pos.le
  have hT : TO ≤ b := le_trans B.TO_le_sb B.sb_le_b
  have hrd : rd ^ 2 ≤ b := le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hP : PP ≤ b := le_trans B.PP_le_sb B.sb_le_b
  have hd2 := h.d_sq hd0 hd
  have hk2 : (0 : ℝ) ≤ 1250 * k ^ 2 := by positivity
  have s1 : TO * (1250 * r) ≤ b * (1250 * k ^ 2) :=
    mul_le_mul hT (by linarith [h.r_le]) (by linarith [h.r6]) hb0
  have n1 : 0 ≤ b * (1250 * k ^ 2) := mul_nonneg hb0 hk2
  have s2 : TO * (1250 * r) * rd ^ 2 ≤ b * (1250 * k ^ 2) * b := mul_le_mul s1 hrd (sq_nonneg rd) n1
  have n2 : 0 ≤ b * (1250 * k ^ 2) * b := mul_nonneg n1 hb0
  have s3 : TO * (1250 * r) * rd ^ 2 * PP ≤ b * (1250 * k ^ 2) * b * b := mul_le_mul s2 hP h.PP_pos.le n2
  have n3 : 0 ≤ b * (1250 * k ^ 2) * b * b := mul_nonneg n2 hb0
  have s4 : TO * (1250 * r) * rd ^ 2 * PP * d ^ 2 ≤ b * (1250 * k ^ 2) * b * b * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul s3 hd2 (sq_nonneg d) n3
  have s5 : 20000 * k ^ 6 * b ^ 5 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : b * (1250 * k ^ 2) * b * b * (16 * k ^ 4 * b ^ 2) = 20000 * k ^ 6 * b ^ 5 := by ring
  linarith

theorem h3e {d q fm : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    2 * (fm * (rd ^ 2) ^ 2 * (rd ^ 2 * PP * d ^ 2)) ≤ q := by
  have B := h.toBs
  have hb0 := h.b_pos.le
  have hrd4 : (rd ^ 2) ^ 2 ≤ b := by
    have : (rd ^ 2) ^ 2 = rd ^ 4 := by ring
    rw [this]; exact le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hrd : rd ^ 2 ≤ b := le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hP : PP ≤ b := le_trans B.PP_le_sb B.sb_le_b
  have hd2 := h.d_sq hd0 hd
  have hPP0 := h.PP_pos.le
  have t1 : fm * (rd ^ 2) ^ 2 ≤ k ^ 4 * b := mul_le_mul hf hrd4 (by positivity) (by positivity)
  have t2 : rd ^ 2 * PP ≤ b * b := mul_le_mul hrd hP hPP0 hb0
  have t3 : rd ^ 2 * PP * d ^ 2 ≤ b * b * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul t2 hd2 (sq_nonneg d) (mul_nonneg hb0 hb0)
  have t4 : fm * (rd ^ 2) ^ 2 * (rd ^ 2 * PP * d ^ 2) ≤ k ^ 4 * b * (b * b * (16 * k ^ 4 * b ^ 2)) :=
    mul_le_mul t1 t3 (mul_nonneg (mul_nonneg (sq_nonneg rd) hPP0) (sq_nonneg d)) (mul_nonneg (by positivity) hb0)
  have t5 : 32 * k ^ 8 * b ^ 5 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : 2 * (k ^ 4 * b * (b * b * (16 * k ^ 4 * b ^ 2))) = 32 * k ^ 8 * b ^ 5 := by ring
  linarith

theorem h3f {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) : (D2 + 2) * d ≤ q - 2 := by
  have B := h.toBs
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) B.b_ge
  have hT : TO ≤ b := le_trans B.TO_le_sb B.sb_le_b
  have h1 : D2 + 2 ≤ 2 * b := by linarith [h.forty_mul_degree_le_order, h.one_le_order_alt, B.b_ge]
  have h2 := h.d_le hd
  have h3 : (D2 + 2) * d ≤ 2 * b * (4 * k ^ 2 * b) := mul_le_mul h1 h2 hd0 (by linarith)
  have hk1 : (1 : ℝ) ≤ k ^ 2 := by nlinarith [h.k1]
  have hb2 : (1 : ℝ) ≤ b ^ 2 := by nlinarith
  have h4 : 1 * 1 ≤ k ^ 2 * b ^ 2 := mul_le_mul hk1 hb2 zero_le_one (by linarith)
  have h5 : 10 * k ^ 2 * b ^ 2 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith

theorem g_gt {s q : ℝ} (hs : s ≤ 4 * A * b) (hq : (k * b) ^ 8 ≤ q) : 2 * s + 2 < q := by
  have B := h.toBs
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) B.b_ge
  have h1 : A * b ≤ 2 * k ^ 2 * b := mul_le_mul_of_nonneg_right h.Ak (by linarith)
  have hk : (64 : ℝ) ≤ k ^ 2 := by nlinarith [h.k8]
  have h2 : 64 * 1 ≤ k ^ 2 * b := mul_le_mul hk hb1 zero_le_one (by linarith)
  have h3 : 18 * k ^ 2 * b ^ 1 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : b ^ 1 = b := pow_one b
  rw [h4] at h3
  linarith

end Rn

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def q0N (T : ParamsT D L P) : ℕ := ⌈L.sc.b / (T.TO : ℝ)⌉₊

theorem f_ge (D : D7) : 8 ≤ D.R.f := by
  have he : 2 ≤ D.R.toFrame.e := D.host.two_le_e
  have hU : Nat.card (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ = 2 ^ (D.R.toFrame.e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      show D.R.toFrame.e + 2 = (D.R.toFrame.e + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hH : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ))
  rw [hU] at hmul
  have hidx : 2 ^ D.R.toFrame.e ≤ (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := by
    have h2 : 2 ^ (D.R.toFrame.e + 1) = 2 * 2 ^ D.R.toFrame.e := by ring
    nlinarith
  have hsurj := Nat.card_le_card_of_surjective _ D.R.toFrame.projection_surjective_field
  have hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp D.R.toFrame.e)) =
      (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := rfl
  have hfin : Nat.card (Formalism.HC.Idx D.R.toFrame.ord) = D.R.toFrame.ord := by
    unfold Formalism.HC.Idx
    simp
  rw [hcard, hfin] at hsurj
  have h4 : 4 ≤ 2 ^ D.R.toFrame.e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.R.toFrame.e := Nat.pow_le_pow_right (by norm_num) he
  unfold Ranks.f Ranks.n
  omega

theorem r_ge (D : D7) : 6 ≤ D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  have := D.R.m_add_three_le_k
  omega

theorem r_le_2k (D : D7) : D.R.r ≤ 2 * D.R.k := by
  unfold Ranks.r
  have := D.R.m_add_three_le_k
  omega

theorem f_le_k (D : D7) : D.R.f ≤ D.R.k := by
  unfold Ranks.f Ranks.n
  exact D.R.f_le_k

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem A_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  unfold zBase
  exact le_mul_of_one_le_right (by positivity) (one_le_L L)

theorem zBase_pow_twelve_le (T : ParamsT D L P) (hZ : 1 ≤ zBase L) : zBase L ^ 12 ≤ T.PP := by
  rw [T.PP_eq]
  have h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP := Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge
  have h3 : 0 ≤ zBase L ^ T.eP := Real.rpow_nonneg (by linarith) _
  have h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP := mul_le_mul_of_nonneg_right T.one_le_CP h3
  rw [h1]
  linarith

theorem discriminant_pow_eight_le_sqrt (P : ParameterChoice' D L) (S : SizesAt L) : D.host.rdE ^ 8 ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩ := S
  obtain ⟨-, -, -, -, -, -, hrd1, hrd2⟩ := hQD
  have hc := P.condE_le
  simp only [Formalism.BasicNotions.LevelStarExponents.condE] at hc
  push_cast at hc
  have hq : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by nlinarith
    have h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  have h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 :=
    pow_le_pow_left₀ (by linarith) hrdC 8
  have h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    pow_le_pow_right₀ hC1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := by positivity
  nlinarith

theorem rn_of (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) :
    Rn ((D.R.f : ℝ) * D.R.r) D.R.k L.sc.b (L.sc.b ^ ((1 : ℝ) / 2)) T.PP T.TO D.host.rdE D.R.r ((T.Dp : ℝ) + 2) T.nWn T.nP
      (q0N T) := by
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast r_le_2k D
  have hz1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hz12 := zBase_pow_twelve_le T hz1
  have hAZ := A_le_Z L
  have hzz2 : zBase L ^ 2 ≤ zBase L ^ 12 := by
    first
    | exact pow_le_pow_right₀ hz1 (by norm_num)
    | exact pow_le_pow_right hz1 (by norm_num)
  have hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP := by
    have h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L :=
      mul_le_mul hZ hAZ (by positivity) (by linarith)
    nlinarith
  have hTO40 := T.TO_40
  have hTOpos : (0 : ℝ) < T.TO := by exact_mod_cast (by omega : 0 < T.TO)
  have hb := b_pos L
  have hrd1 : (1 : ℝ) ≤ D.host.rdE := by
    have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
      have h := NumberField.discr_ne_zero D.host.E
      have h' : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
      exact_mod_cast h'
    unfold Host.rdE
    exact Real.one_le_rpow hd (by positivity)
  have hnW : 40 ≤ T.nWn := by
    have h1 := T.nW_lo.1
    have h2 := f_ge D
    have h3 := r_ge D
    have h4 : 8 * 6 ≤ D.R.f * D.R.r := Nat.mul_le_mul h2 h3
    have h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      first
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | exact Nat.le_mul_of_pos_right (by omega)
    generalize D.R.f * D.R.r * (D.R.r + 1) = X at *
    generalize D.R.f * D.R.r = Y at *
    omega
  have hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ) := by
    unfold q0N
    have h := Nat.le_ceil (L.sc.b / T.TO)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b := by
      field_simp
    calc L.sc.b = (T.TO : ℝ) * (L.sc.b / T.TO) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h hTOpos.le
  have hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO := by
    unfold q0N
    have h := Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO := by
      field_simp
      try ring
    have := mul_le_mul_of_nonneg_left h.le hTOpos.le
    linarith
  exact
    { forty_eight_le_constant := by nlinarith
      k8 := by linarith
      Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      sb_sq := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.mul_self_sqrt hb.le
      PPA := hPPA
      h32 := T.precision_cube_order_sq_le_sqrt
      hTP := T.TO_PP'
      one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)
      rd1 := hrd1
      rd8 := discriminant_pow_eight_le_sqrt P S
      r6 := hr6
      rA := by nlinarith
      two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith
      W := by exact_mod_cast T.TO_nW
      forty_mul_degree_le_order := by exact_mod_cast T.TO_40
      forty_le_weight_count := by exact_mod_cast hnW
      projectivePointSizes := Nat.cast_nonneg _
      nPW := by exact_mod_cast T.nW_lo.2.2
      q0lo := hq0lo
      q0hi := hq0hi }

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
