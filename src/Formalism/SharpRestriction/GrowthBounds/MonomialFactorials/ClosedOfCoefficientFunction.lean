module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExistsHigh
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthogonalityWindow
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromNineToEight
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromEightToSeven
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromSevenToSix
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PositiveOfDimensionChange
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DirectionsOfPositivePart
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ThresholdsMonoNormalized
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.EpsilonBoundMConstant
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem eps_num (Sr Yr Y κ lg CM : ℝ) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (15 + CM) / Y := by
  have hY0 : 0 < Y := by linarith
  have e1 : (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) = CM / Y + 2 * (Sr / Yr) * (lg / κ) / Y := by
    field_simp
  rw [e1]
  have h1 : lg / κ ≤ 1 / 24 := by rw [div_le_iff₀ hκ]; linarith
  have h2 : 0 ≤ Sr / Yr := div_nonneg hS0 hYr.le
  have h3 : 0 ≤ lg / κ := div_nonneg hlg hκ.le
  have h4 : 2 * (Sr / Yr) * (lg / κ) ≤ 2 * (7 / Y) * (1 / 24) := by gcongr
  have h5 : 7 / Y ≤ 7 := by rw [div_le_iff₀ hY0]; nlinarith
  have h6 : 2 * (Sr / Yr) * (lg / κ) / Y ≤ 1 / Y := by
    apply div_le_div_of_nonneg_right _ hY0.le
    nlinarith
  have h7 : 2 * Sr / Yr = 2 * (Sr / Yr) := by ring
  rw [h7]
  have h8 : 2 * (Sr / Yr) ≤ 14 / Y := by
    have : 2 * (7 / Y) = 14 / Y := by ring
    linarith
  have e2 : (15 + CM) / Y = 14 / Y + CM / Y + 1 / Y := by ring
  rw [e2]
  linarith

theorem epsilon_bound_M_constant (Sr Yr Y κ lg CM : ℝ) (hCM : 1 ≤ CM) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (2 * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (30 + CM) / Y := by
  refine (eps_num Sr Yr Y κ lg 2 hY hYr hS0 hSY hκ hlg hlk).trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure EpsFacts (C0 : ℝ) (X : flipOneThree.Inst) : Prop where
  pk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.p : ℝ)
  kYb : X.L.k * X.L.Y ^ 2 * X.L.b' ≤ X.L.a / 2

theorem epsFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hb5 : (X.r : ℝ) + 1 ≤ X.L.b') : EpsFacts C0 X := by
  obtain ⟨h0, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, -, hN1, -, -, hb0, -, -, -, -, hYb, -, hlog, -⟩ := h0
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hr5 := r5 hS
  have hkb := hS.kb
  have ha100 : (100 : ℝ) ≤ X.L.a := by
    have h25 : (25 : ℝ) ≤ ((X.r : ℝ) + 1) * X.L.b' := by nlinarith only [hr5, hb5]
    linarith
  have hloga : 1 ≤ Real.log X.L.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLa : 1 ≤ X.L.La C0 := by
    show 1 ≤ lambdaScale C0 X.L.N1 X.L.a
    unfold lambdaScale
    have h1 : (1 : ℝ) ≤ (X.L.N1 : ℝ) := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ (X.L.N1 : ℝ) ^ 2 := one_le_pow₀ h1
    have h3 := one_le_mul_of_one_le_of_one_le hC0 h2
    exact one_le_mul_of_one_le_of_one_le h3 hloga
  have hYb2 : (2 : ℝ) ≤ X.L.Yb := le_trans hCYb hYb
  refine ⟨hpk, ?_⟩
  have h1 : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right hlog hb0.le
    rwa [div_mul_cancel₀ _ hb0.ne'] at this
  have hM : 2 ≤ X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a := by
    have h4 : (1 : ℝ) ≤ X.L.N * X.L.La C0 * Real.log X.L.a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hLa) hloga
    nlinarith only [hYb2, h4]
  have h3 : 0 ≤ X.L.k * X.L.Y ^ 2 * X.L.b' := by
    have : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have := hb0.le
    positivity
  have e : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' =
      (X.L.k * X.L.Y ^ 2 * X.L.b') * (X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a) := by ring
  rw [e] at h1
  have h5 := mul_le_mul_of_nonneg_left hM h3
  linarith

theorem restTMEps_of (hS : SegFacts C0 CE1 CE2 X) (hE' : (X.r : ℝ) + 1 ≤ X.L.b' → EpsFacts C0 X)
    (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM := by
  intro dl hdl a ha x hx i
  have hk : X.L.k = (X.r : ℝ) + 1 := rfl
  have hk0 : X.L.k ≠ 0 := by rw [hk]; have := r5 hS; linarith
  have hY0 : X.L.Y ≠ 0 := by have := hS.Y1; linarith
  have hr5 := r5 hS
  have hY := hS.Y1
  have hb0 := hS.hF.b0
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP : ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.b' := hS.kP _
  have hb5 : (X.r : ℝ) + 1 ≤ X.L.b' := by
    have := mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ (X.r : ℝ) + 1)
    linarith
  have hkY0 : 0 < X.L.k * X.L.Y := by rw [hk]; exact mul_pos (by linarith) (by linarith)
  have hE := hE' hb5
  have hkYb := hE.kYb
  have h4Y : 4 * X.L.Y ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; nlinarith only [hr5, hY]
  have hYb' : 4 * X.L.Y * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right h4Y hb0.le
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    linarith
  have hroomR : (X.L.a : ℝ) + 2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      X.L.a + X.L.a / (X.L.k * X.L.Y) - 1 := by
    have h1 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k ≤ 3 * X.L.b' := by
      rw [hk]; nlinarith only [hkP, hb5]
    have h2 : 3 * X.L.b' * X.L.Y ≤ X.L.a := by nlinarith only [hYb', hY, hb0]
    have h3 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) ≤ X.L.a / (X.L.k * X.L.Y) := by
      rw [le_div_iff₀ hkY0]
      have : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * (X.L.k * X.L.Y) =
          ((2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k) * X.L.Y := by ring
      rw [this]
      nlinarith only [h1, h2, hY]
    linarith
  have hwin : (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) - 1 <
      ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
    have := hS.xa0
    linarith
  have hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := hS.xa0
    linarith
  have hYl := Yl_bound hS hFree hdl ha hx i hroom
  have hYP : X.L.a / (2 * (X.L.k * X.L.Y)) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    have h1 : 1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.a / (2 * (X.L.k * X.L.Y)) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1) ≤ 2 * X.L.b' := by
        nlinarith only [hkP, hb5]
      rw [hk]
      have : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * (2 * (((X.r : ℝ) + 1) * X.L.Y)) =
          2 * X.L.Y * ((1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1)) := by ring
      rw [this]
      nlinarith only [h2, hYb', hY]
    have h4 : X.L.a / (X.L.k * X.L.Y) = 2 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by field_simp
    linarith
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  have hT' := (mem_cbox' ha').1
  have hSB := S_bound hS _ hT' x.1 hK' x.2 i
  have eS : (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
      (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i =
      (gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i := by
    rw [setTies_top ha hx]
    rfl
  unfold epsM flipOneThree.InstM.eps flipOneThree.InstM.Si flipOneThree.InstM.LLt
  rw [eS]
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by nlinarith only [hp, hr5]
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hB2 : 0 < X.L.a / (2 * (X.L.k * X.L.Y)) := by
    have : (0 : ℝ) < X.L.a := by nlinarith only [hYb', hY, hb0]
    positivity
  have hYr0 : (0 : ℝ) < ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) := by
    have h2 := lt_of_lt_of_le hB2 hYP
    exact pos_of_mul_pos_left h2 (by linarith)
  have hB1 : 0 ≤ 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    positivity
  have hfin : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y ≤ 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by
    have hq : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) ≤ 4 * X.L.a := by
      have hpk' := hE.pk
      have h1 : (2 * (X.s : ℝ) + 1) ≤ X.L.k := by rw [hk]; linarith
      have e3 : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) =
          4 * X.L.a * ((2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2) / X.p := by ring
      rw [e3, div_le_iff₀ hp0]
      have h2 : (2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2 ≤ X.L.k ^ 2 * X.L.Y ^ 2 := by
        have : 0 ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; positivity
        nlinarith only [h1, this]
      have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
      nlinarith only [h2, hpk', ha0]
    have hq2 : 5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2) ≤ 5 / 2 * X.L.a := by nlinarith only [hkYb]
    have e4 : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y =
        ((5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2)) + (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2)) /
          (2 * (X.L.k * X.L.Y)) := by
      field_simp
    rw [e4, div_le_iff₀ (by positivity)]
    have e5 : 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) * (2 * (X.L.k * X.L.Y)) = 7 * X.L.a := by field_simp
    rw [e5]
    linarith
  have hSY : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) /
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) ≤ 7 / X.L.Y := by
    have hPp : (0 : ℝ) < ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by linarith
    rw [div_le_div_iff₀ hYr0 (by linarith)]
    have h1 : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y ≤
        7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_right hSB (by linarith : (0 : ℝ) ≤ X.L.Y)
      have h3 := mul_le_mul_of_nonneg_left hYP (by norm_num : (0 : ℝ) ≤ 7)
      linarith
    have e : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y =
        (((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * X.L.Y) *
          ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by ring
    have e2 : 7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) =
        (7 * ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ)) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      ring
    rw [e, e2] at h1
    exact le_of_mul_le_mul_right h1 hPp
  have hlg1 : 1 ≤ lgA X.p X.L.a X.r := lgA_ge_one_facts hS.hF
  have hκ : 24 * lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    have h1 : (2 : ℝ) ≤ (X.r : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
    have h3 : (4 : ℝ) ≤ (X.r : ℝ) ^ 2 := by nlinarith only [h1]
    have h4 : (6 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) := by linarith
    have h5 : (24 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith only [h3, h4]
    nlinarith only [h5, hlg1]
  exact epsilon_bound_M_constant _ _ X.L.Y (kapS X) (lgA X.p X.L.a X.r) CM hCM hY hYr0 (Nat.cast_nonneg _) hSY (by linarith) (by linarith) hκ

theorem restTMEps_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM :=
  restTMEps_of hS (epsFacts hCYb hC0 hH hS) hFree CM hCM

theorem restTM_closed : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    2 ≤ CYb → 1 ≤ Cb → 0 ≤ CD → 1 ≤ C0 → 0 ≤ CE1 → 0 ≤ CE2 →
      flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestTM C0 CE1 CE2 X CM := by
  obtain ⟨CM, hCM, h⟩ := restTM_exists
  refine ⟨CM, hCM, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hYb hCb hCD hC0 hE1 hE2 hH => ?_⟩
  have hS := segFacts hYb hCb hCD hE1 hE2 hH (CE1 := CE1) (CE2 := CE2)
  have hF := restFree_proved hS
  exact h D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF (restTMSize_proved hS hF)
    (restTMEps_proved hYb hC0 hH hS hF CM hCM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOpenConditions
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SegmentWeightedCountingBoundOfAllRemainingBounds
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports
namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset

theorem assemble {α ι Z : Type*} (A : Finset α) (Wn : Finset ℕ) (I : Finset Z) (T : Finset ι)
    (bl : α → ℕ → Z → ℝ) (bq : α → Z → ℝ) (dx : Z → ℝ) (dy : α → Z → ℝ) (u : α → ι → α) (m : α → ℝ)
    (ε₁ ε₂ K : ℝ) (h1 : 0 ≤ ε₁) (h2 : 0 ≤ ε₂) (hdx : ∀ z, 0 ≤ dx z)
    (hplus : ∀ a ∈ A, ∀ z ∈ I, ∑ w ∈ Wn, bl a w z ≤ (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)))
    (htm : ∀ z ∈ I, ∑ a ∈ A, bq a z ≤ ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z)
    (hcnt : ∀ a ∈ A, ∑ z ∈ I, dy a z * dx z ≤ m a)
    (hu : ∀ a ∈ A, ∀ i ∈ T, u a i ∈ A ∧ m (u a i) ≤ K * m a) :
    ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤ (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by
  have hS1 : ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤
      ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := by
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun z hz => hplus a ha z hz
  have hQ : ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z ≤ ε₁ * T.card * K * ∑ a ∈ A, m a := by
    calc ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z = ∑ z ∈ I, ∑ a ∈ A, bq a z * dx z := Finset.sum_comm
      _ = ∑ z ∈ I, (∑ a ∈ A, bq a z) * dx z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_mul]
      _ ≤ ∑ z ∈ I, (ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z) * dx z := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (htm z hz) (hdx z)
      _ = ∑ z ∈ I, ∑ i ∈ T, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ T, ∑ z ∈ I, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := Finset.sum_comm
      _ = ∑ i ∈ T, ∑ a ∈ A, ∑ z ∈ I, ε₁ * (dy (u a i) z * dx z) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ ≤ ∑ i ∈ T, ∑ a ∈ A, ε₁ * (K * m a) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro a ha
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ h1
          exact (hcnt (u a i) (hu a ha i hi).1).trans (hu a ha i hi).2
      _ = ∑ i ∈ T, ε₁ * (K * ∑ a ∈ A, m a) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ε₁ * T.card * K * ∑ a ∈ A, m a := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hD : ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z) ≤ ε₂ * ∑ a ∈ A, m a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcnt a ha) h2
  calc ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z
      ≤ ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := hS1
    _ = (Wn.card : ℝ) * (∑ a ∈ A, ∑ z ∈ I, bq a z * dx z
          + ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z)) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (Wn.card : ℝ) * (ε₁ * T.card * K * ∑ a ∈ A, m a + ε₂ * ∑ a ∈ A, m a) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ hD) (Nat.cast_nonneg _)
    _ = (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by ring

end Formalism.MainNotions.G.SymmetricFormBlocks
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem rank_le {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) (dl : DCl X)
    (hc : Compat C0 CE1 CE2 X dl aTop) :
    clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl ≤ mCl C0 CE1 CE2 X dl aTop := by
  have hIn := realise hH aTop aPlus hT hP
  have hm0 : 0 ≤ X.m := hH.2.2.2.2.2.2.2.2.1
  have hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) := hH.2.2.2.2.2.2.2.2.2
  have h := h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2
  rw [rankOnDigits_eq, realW_top, realW_plus] at h
  exact (h hc).2

theorem mem_cbox {dl : DCl X} {aTop : Fin X.s → ℕ} :
    aTop ∈ cbox C0 CE1 CE2 X dl ↔
      aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem clSum_levels (dl : DCl X) (aTop : Fin X.s → ℕ) (f : SegBlock X.s X.r → Lv C0 CE1 CE2 X → ℕ) :
    ((clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, f b x) aTop dl : ℕ) : ℝ) =
      ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (f z.1 z.2 : ℝ) := by
  rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
  unfold idx keptSet
  rw [Finset.sum_sigma]
  push_cast
  rfl

theorem claim2 {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hDir : RestDir C0 CE1 CE2 X) (hW : X.winA.Nonempty)
    (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) ≤ (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
  obtain ⟨aPlus, hP⟩ := hW
  obtain ⟨hT, hc⟩ := mem_cbox.1 ha
  rw [← clSum_levels dl aTop (fun b x => rL C0 CE1 CE2 X aTop b x)]
  have h1 : clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x) aTop dl ≤
      clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl := by
    rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop), clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
    refine Finset.sum_le_sum fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b :=
      (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop).mem_toFinset.1 (Finset.mem_filter.1 hb).1
    exact hDir aTop hT aPlus hP b hk
  exact_mod_cast h1.trans (rank_le hH h11 aTop aPlus hT hP dl hc)

theorem digit_class_dimension_comparison_of_remaining_estimates {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (CM : ℝ) (hCM : 0 ≤ CM)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hPlus : RestPlus C0 CE1 CE2 X CM) (hTM : RestTM C0 CE1 CE2 X CM) (hDir : RestDir C0 CE1 CE2 X)
    (hFree : RestFree C0 CE1 CE2 X) (hRat : RestRatio C0 CE1 CE2 X) :
    DigitClassDimensionComparison C0 CE1 CE2 X (fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
      ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) := by
  classical
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  intro dl hdl
  have hbox : (CountingStatementReduction.box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1) = cbox C0 CE1 CE2 X dl ×ˢ X.winA := by
    ext a
    simp only [CountingStatementReduction.box, Finset.mem_filter, Finset.mem_product, mem_cbox]
    tauto
  rw [hbox, Finset.sum_product, Finset.sum_product]
  have hR : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ _aPlus ∈ X.winA, (mCl C0 CE1 CE2 X dl aTop : ℝ) =
      (X.winA.card : ℝ) * ∑ aTop ∈ cbox C0 CE1 CE2 X dl, (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hR]
  by_cases hW : X.winA.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hW
    simp [hW]
  by_cases hA : (cbox C0 CE1 CE2 X dl).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [hA]
  obtain ⟨a0, ha0⟩ := hA
  have hL : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA,
        ((clSum C0 CE1 CE2 X (fun b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋) aTop dl : ℕ) : ℝ) =
      ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ∑ z ∈ idx C0 CE1 CE2 X dl a0,
        (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    refine Finset.sum_congr rfl fun aTop ha => Finset.sum_congr rfl fun aPlus _ => ?_
    rw [← hFree dl hdl aTop ha a0 ha0]
    exact clSum_levels dl aTop (fun b x => bLvl C0 CE1 CE2 X aTop aPlus b x ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
  rw [hL]
  have key := assemble (cbox C0 CE1 CE2 X dl) X.winA (idx C0 CE1 CE2 X dl a0)
    (Finset.univ : Finset (Fin (X.S C0 CE1 CE2).t))
    (fun aTop aPlus z => (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun aTop z => (bY C0 CE1 CE2 X aTop z.1 z.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun z => (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ))
    (fun aTop z => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ))
    (fun aTop i => upd C0 CE1 CE2 X dl aTop i)
    (fun aTop => (mCl C0 CE1 CE2 X dl aTop : ℝ))
    ((30 + CM) / X.L.Y) (5 / X.L.Y) (Real.exp 3) (by positivity) (by positivity) (fun z => Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fin] at key
    exact key
  · intro aTop ha z hz
    have h := hPlus dl hdl aTop ha z (by rw [hFree dl hdl aTop ha a0 ha0]; exact hz)
    have e : (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) =
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ) *
          (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ) := by
      unfold rL
      push_cast
      rfl
    rw [e] at h
    exact h
  · intro z hz
    exact hTM dl hdl a0 ha0 z hz
  · intro aTop ha
    have h := claim2 hH h11 hDir hW dl aTop ha
    rw [hFree dl hdl aTop ha a0 ha0] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold rL
    push_cast
    rfl
  · intro aTop ha i _
    exact hRat dl hdl aTop ha i

def RestAll (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X ∧
      RestFree C0 CE1 CE2 X ∧ RestRatio C0 CE1 CE2 X ∧ RestDepth C0 CE1 CE2 X CM C

theorem segment_weighted_counting_bound_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) (hCM : 0 ≤ CM)
    (hC : 2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hR : RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X) : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH _
  obtain ⟨hBlk, hPlus, hTM, hDir, hFree, hRat, hD0, hDep⟩ := hR hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  refine ⟨fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋,
    (30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y, by positivity, ?_, ?_,
    digit_class_dimension_comparison_of_remaining_estimates CM hCM hH h11 hPlus hTM hDir hFree hRat⟩
  · have e1 : 2 * ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) * Real.exp 3 =
        2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3 / X.L.Y := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_right _ hY0.le
    have h1 : (30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 ≤
        ((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by
      have : 0 ≤ (30 + CM) * Real.exp 3 := by positivity
      nlinarith
    have h2 : 0 ≤ (30 + CM) * Real.exp 3 + 5 := by positivity
    calc 2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3
        ≤ 2 * (((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1)) * Real.exp 3 := by
          apply mul_le_mul_of_nonneg_right _ he.le
          linarith
      _ = (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by ring
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := mul_le_mul_of_nonneg_right hC (by linarith)
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by
          have : 0 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) :=
            mul_nonneg (le_trans (by positivity) hC) (by linarith)
          nlinarith
  · intro aTop hT aPlus hP b hk
    have h0 : (0 : ℤ) ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.2 (mul_nonneg hY0.le hD0)
    obtain ⟨L₂, hg, hr⟩ := hBlk aTop hT aPlus hP b hk _ h0
    refine ⟨L₂, GoodSub_mono ?_ hg, hr⟩
    have := Int.floor_le (X.L.Y * D1r C0 CE1 CE2 X CM)
    linarith

def RestAllE (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM C : ℝ, 0 ≤ CM ∧ 1 ≤ C ∧
    2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X

theorem rest1DAE_of (D : Formalism.BasicNotions.D7) (h : RestAllE D) : DigitClassRemainingUniform D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 Ckap Cs => by
    obtain ⟨CM, C, hCM, hC1, hC, h2⟩ := h1 Ckap Cs
    exact ⟨C, hC1, fun X hA =>
      segment_weighted_counting_bound_of_all_remaining_bounds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X hCM hC hA.2.2.2.2.2.2 (h2 X hA)⟩) h

theorem theorem_A_closed_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (h : RestAllE D) : IntegralityFromMetricForLargeConstants D :=
  counting_statement_uniform_of_digit_class D (rest1DAE_of D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thr_mono_seg {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : flipOneThree.TransportedAlt P) : flipOneThree.TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  have m1 := le_max_left T2 2
  have m2 := le_max_right T2 2
  exact h _ _ _ _ _ _ _ _ _ (m2.trans b1) (by linarith) (by linarith) (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (m1.trans b1) (m1.trans b2) (m1.trans b3) (m1.trans b4) (m1.trans b5))

def RestOpen (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpenE (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM : ℝ, 0 ≤ CM ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restAllE_of_open (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : RestAllE D :=
  thr_mono_seg (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY hD hb h1 h2 hP Ckap Cs => by
    obtain ⟨CM, hCM, hX⟩ := hP Ckap Cs
    have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
    refine ⟨CM, max (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) (18 * (1 + CM) + 20), hCM,
      le_max_of_le_right (by linarith), le_max_left _ _, fun X hA hH => ?_⟩
    obtain ⟨a, b, c, d⟩ := hX X hA hH
    have hS := segFacts hY hb hD h1 h2 hH
    exact ⟨a, b, c, d, restFree_proved hS, ratioCondition_of_segFacts hS,
      restDepth_proved CM _ (by linarith) hCM (le_max_right _ _) hH⟩) h

theorem closed_of_open_conditions (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_all_remaining_bounds D (restAllE_of_open D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thresholds_mono_normalized {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ C0 → 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : flipOneThree.TransportedAlt P) : flipOneThree.TransportedAlt Q := by
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at hP ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨max T0 1, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 (le_trans (le_max_left _ _) hC0)
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb hY hde hk hD hb => ?_⟩
  have hT2' : T2 ≤ max T2 2 := le_max_left _ _
  have h2' : (2 : ℝ) ≤ max T2 2 := le_max_right _ _
  have h1' : (1 : ℝ) ≤ max T0 1 := le_max_right _ _
  exact h C0 CYb Cde Ck CD Cb CE1 CE2 Cc (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (hT2'.trans hY) (hT2'.trans hde) (hT2'.trans hk) (hT2'.trans hD) (hT2'.trans hb))

def RestOpen4 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusA C0 CE1 CE2 X CM ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen4E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen4 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem openE_of_open4 (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : RestOpenE D := by
  obtain ⟨CM, hCM, hTM⟩ := restTM_closed
  exact thresholds_mono_normalized (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hC0 hY hD hb h1 h2 hP Ckap Cs =>
    ⟨CM, by linarith, fun X hA hH => by
      obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
      have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
      exact ⟨block_bound_of_dual_families C0 CE1 CE2 X (block_valuation_over_Zp_holds C0 CE1 CE2 X (by linarith) h1 h2 hH) a,
        restPlus_of CM hY0 b (restRankL_proved C0 CE1 CE2 X) c,
        hTM D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hY hb hD hC0 h1 h2 hH, d⟩⟩) h

theorem closed_of_open_directions (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_conditions D (openE_of_open4 D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen5 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen5E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen5 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem directions_of_positive_part (D : Formalism.BasicNotions.D7) (h : RestOpen5E D) : RestOpen4E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, plusACondition C0 CE1 CE2 X CM, b, c⟩) h

theorem closed_of_open_positive (D : Formalism.BasicNotions.D7) (h : RestOpen5E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_directions D (directions_of_positive_part D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen6 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen6E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen6 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem positive_of_dimension_change (D : Formalism.BasicNotions.D7) (h : RestOpen6E D) : RestOpen5E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, restDir_of c (restDimBC_proved C0 CE1 CE2 X)⟩) h

theorem closed_of_open_dimensions (D : Formalism.BasicNotions.D7) (h : RestOpen6E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_positive D (positive_of_dimension_change D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen7 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen7E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen7 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_seven_to_six (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : RestOpen6E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
    exact ⟨a, restPlusB_of CM hY0 b c, d⟩) h

theorem closed_of_open_base_dims (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_dimensions D (restricted_bounds_weaken_from_seven_to_six D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen8 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen8E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen8 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_eight_to_seven (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : RestOpen7E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBCdim_of C0 CE1 CE2 X a, b, c, d⟩) h

theorem theorem_A_closed_of_eight_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_base_dims D (restricted_bounds_weaken_from_eight_to_seven D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen9 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def RestOpen9E (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen9 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_nine_to_eight (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : RestOpen8E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, c, restDirQ_of d (restSumSpan_proved C0 CE1 CE2 X)⟩) h

theorem theorem_A_closed_of_nine_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_eight_open_bounds D (restricted_bounds_weaken_from_nine_to_eight D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- restored from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestBCdimOfYbc
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

private theorem finrank_span_blockData_gens {p : ℕ} [Fact (Nat.Prime p)] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : ℚ_[p] →+* KK O) {N r : ℕ} [NeZero r] (hY : RestYbc)
    (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp)) ≤
      Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := by
  classical
  let W : Submodule ℚ_[p] (MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p]) :=
    Submodule.span ℚ_[p] (SetLike.coe (Ljj (r := r) p (gmB D) j jp))
  haveI hWfd : FiniteDimensional ℚ_[p] W := Ljj_span_fd (p := p) (r := r) (gmB D) j jp
  let Pk : MvPolynomial (BVar N r D.T.t) (KK O) :=
    ((∏ i : Fin D.T.t, BlockData.Ehat (r := r) O D i ^ j i) * BlockData.Eplus (r := r) O D ^ jp *
      ∏ i : Fin D.T.t, MvPolynomial.X (scalZ N r D.T.t i.castSucc) ^ D.T.z i) *
      MvPolynomial.X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus
  let mι : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+* MvPolynomial (BVar N r D.T.t) (KK O) :=
    MvPolynomial.map ι
  let fA : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+ MvPolynomial (BVar N r D.T.t) (KK O) :=
    (AddMonoidHom.mulLeft Pk).comp mι.toAddMonoidHom
  have hfA : ∀ u, fA u = Pk * mι u := fun u => rfl
  have hadd : ∀ u v, fA (u + v) = fA u + fA v := fun u v => map_add fA u v
  have hsmul : ∀ (c : ℚ_[p]) u, fA (c • u) = ι c • fA u := by
    intro c u
    rw [hfA, hfA, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [mι, MvPolynomial.map_C]
    ring
  let T : Submodule (KK O) (MvPolynomial (BVar N r D.T.t) (KK O)) :=
    Submodule.span (KK O) (fA '' (W : Set _))
  have hT : Module.finrank (KK O) T ≤ Module.finrank ℚ_[p] W :=
    finrank_span_image_le ι fA hadd hsmul W
  let bW := Module.finBasis ℚ_[p] W
  have hTle : T ≤ Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p])) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : MvPolynomial _ ℚ_[p]) := by
      have h1 : ((∑ i, (bW.repr ⟨w, hw⟩ i) • bW i : W) : MvPolynomial _ ℚ_[p]) = w := by
        rw [bW.sum_repr]
      refine h1.symm.trans ?_
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O)
      (Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  haveI : FiniteDimensional (KK O) T :=
    Submodule.finiteDimensional_of_le hTle
  have hbase : ∀ y0 ∈ GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr,
      ∀ g0 ∈ GM.M.XiPolZ p N r D.T.t (D.B - jp),
      Pk * rename (chainEmb N r D.T.t) (MvPolynomial.map ι y0) * MvPolynomial.map ι g0 ∈ T := by
    intro y0 hy0 g0 hg0
    have h1 : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ Ljj (r := r) p (gmB D) j jp := by
      unfold Ljj
      exact Submodule.subset_span ⟨y0, hy0, g0, hg0, rfl⟩
    have hmem : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ W := Submodule.subset_span h1
    have := Submodule.subset_span (R := KK O) (Set.mem_image_of_mem fA hmem)
    rw [hfA] at this
    simp only [mι, map_mul, MvPolynomial.map_rename] at this
    rw [← mul_assoc] at this
    exact this
  have hstep : ∀ a ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr : Set _)),
      ∀ c ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.XiPolZ p N r D.T.t (D.B - jp) : Set _)),
      Pk * rename (chainEmb N r D.T.t) a * c ∈ T := by
    intro a ha c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨g0, hg0, rfl⟩ := hc
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y0, hy0, rfl⟩ := ha
        exact hbase y0 hy0 g0 hg0
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _), mul_add, add_mul]
        exact T.add_mem hx hy
      | smul k x _ hx =>
        rw [map_smul, mul_smul_comm, smul_mul_assoc]
        exact T.smul_mem k hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact T.add_mem hx hy
    | smul k x _ hx =>
      rw [mul_smul_comm]
      exact T.smul_mem k hx
  have hgens : Submodule.span (KK O) (BlockData.gens (r := r) O D j jp) ≤ T := by
    rw [Submodule.span_le]
    rintro x ⟨y, hy, g, hg, rfl⟩
    exact hstep _ (hY O p ι N r (D.lettersAt j jp) D.T.q D.T.J D.T.thr y hy) g (xi_span ι g hg)
  calc Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp))
      ≤ Module.finrank (KK O) T :=
        LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hgens)
          (Submodule.inclusion_injective hgens)
    _ ≤ Module.finrank ℚ_[p] W := hT
    _ = Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := (finrank_Ljj_span (gmB D) j jp).symm

theorem restBClvl_of (hY : RestYbc) : RestBClvl C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _ l _
  exact finrank_span_blockData_gens (O := X.O) (r := X.r) (iotaX X) hY
    (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) l.1 l.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def OpenConditionsOrthogonal (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def OrthogonalityWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → OpenConditionsOrthogonal C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem open_conditions_base_change (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : RestOpen9E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBClvl_of C0 CE1 CE2 X hY, a, b, c⟩) h

theorem integrality_from_metric_of_orthogonality_window (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_nine_open_bounds D (open_conditions_base_change D hY h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryFinitenessWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestLjjFin C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryFinitenessWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryFinitenessWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem orthogonal_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : OrthogonalityWindowLevelDimOnAdmissible D :=
  thr_mono_ge (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hCYb hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
    have hp2 : X.p ≠ 2 := by
      intro h2
      have := p25 hF
      have h3 : (X.L.p : ℝ) = 2 := by exact_mod_cast h2
      linarith
    exact ⟨restOrth_of CM hp2 hO a b, c, d⟩) h

theorem closed_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hY : RestYbc) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  integrality_from_metric_of_orthogonality_window D hY (orthogonal_of_symmetric_finite D hO h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_coefficient_function (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_finite D (restYbc_of_funY hF) hO h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
