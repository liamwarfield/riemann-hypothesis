module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
public import Formalism.PolynomialDimension.DigitClassCount

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensAbs
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

theorem dens_abs (N : ℕ) (hN : 1 ≤ N) (x1 x2 wa wb e : ℝ) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (hwa : 0 < wa) (hwb : 0 < wb)
    (he : 0 ≤ e) (hs : (N : ℝ) * (x1 + x2 + e / wa + e / wb) ≤ 1 / 2) :
    (wa + e) ^ N * (wb + e) ^ N ≤ 2 * ((1 - x1) * (1 - x2)) ^ N * (wa ^ N * wb ^ N) := by
  set u := e / wa with hu
  set v := e / wb with hv
  have hu0 : 0 ≤ u := div_nonneg he hwa.le
  have hv0 : 0 ≤ v := div_nonneg he hwb.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs' : (N : ℝ) * x1 + N * x2 + N * u + N * v ≤ 1 / 2 := by nlinarith
  have hp1 : 0 ≤ (N : ℝ) * u := by positivity
  have hp2 : 0 ≤ (N : ℝ) * v := by positivity
  have hp3 : 0 ≤ (N : ℝ) * x1 := by positivity
  have hp4 : 0 ≤ (N : ℝ) * x2 := by positivity
  have hu1 : u ≤ 1 := by nlinarith
  have hv1 : v ≤ 1 := by nlinarith
  have hx1 : x1 ≤ 1 := by nlinarith
  have hx2 : x2 ≤ 1 := by nlinarith
  have hwa' : wa + e = wa * (1 + u) := by rw [hu]; field_simp
  have hwb' : wb + e = wb * (1 + v) := by rw [hv]; field_simp
  rw [hwa', hwb', mul_pow, mul_pow, mul_pow]

  have hB : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (1 + z) ^ N * (1 - N * z) ≤ 1 := by
    intro z hz0 hz1
    have hb := one_add_mul_le_pow (a := -z) (by linarith) N
    have hzz : (1 + -z) ^ N = (1 - z) ^ N := by ring
    have h1 : (1 + z) ^ N * (1 - z) ^ N ≤ 1 := by
      rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
    have h2 : 0 ≤ (1 + z) ^ N := by positivity
    calc (1 + z) ^ N * (1 - N * z) ≤ (1 + z) ^ N * (1 - z) ^ N :=
          mul_le_mul_of_nonneg_left (by linarith) h2
      _ ≤ 1 := h1
  have hC : ∀ x : ℝ, x ≤ 1 → 1 - N * x ≤ (1 - x) ^ N := by
    intro x hx1
    have hb := one_add_mul_le_pow (a := -x) (by linarith) N
    have hxx : (1 + -x) ^ N = (1 - x) ^ N := by ring
    linarith
  have ha := hB u hu0 hu1
  have hb := hB v hv0 hv1
  have hc := hC x1 hx1
  have hd := hC x2 hx2
  have hA0 : 0 ≤ (1 + u) ^ N := by positivity
  have hB0 : 0 ≤ (1 + v) ^ N := by positivity

  have e1 : 1 - N * u - N * v ≤ (1 - N * u) * (1 - N * v) := by nlinarith [mul_nonneg hp1 hp2]
  have e2 : 1 - N * x1 - N * x2 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith [mul_nonneg hp3 hp4]
  have e3 : (1 - N * u - N * v) * (1 - N * x1 - N * x2) ≤
      (1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)) :=
    mul_le_mul e1 e2 (by linarith) (by nlinarith)
  have e4 : 1 - (N * u + N * v) - (N * x1 + N * x2) ≤ (1 - N * u - N * v) * (1 - N * x1 - N * x2) := by
    nlinarith [mul_nonneg (add_nonneg hp1 hp2) (add_nonneg hp3 hp4)]
  have hprod : 1 ≤ 2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2))) := by linarith
  have hAB : (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v)) ≤ 1 := by
    have := mul_le_one₀ ha (mul_nonneg hB0 (by linarith)) hb
    calc (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))
        = (1 + u) ^ N * (1 - N * u) * ((1 + v) ^ N * (1 - N * v)) := by ring
      _ ≤ 1 := this
  have hCD : (1 - N * x1) * (1 - N * x2) ≤ (1 - x1) ^ N * (1 - x2) ^ N :=
    mul_le_mul hc hd (by linarith) (le_trans (by linarith) hc)
  have key : (1 + u) ^ N * (1 + v) ^ N ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by
    have hγδ : 0 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith
    calc (1 + u) ^ N * (1 + v) ^ N
        ≤ (1 + u) ^ N * (1 + v) ^ N *
            (2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)))) :=
          le_mul_of_one_le_right (mul_nonneg hA0 hB0) hprod
      _ = 2 * ((1 - N * x1) * (1 - N * x2)) *
            ((1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))) := by ring
      _ ≤ 2 * ((1 - N * x1) * (1 - N * x2)) * 1 :=
          mul_le_mul_of_nonneg_left hAB (by linarith)
      _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by linarith
  have hw : 0 ≤ wa ^ N * wb ^ N := by positivity
  calc wa ^ N * (1 + u) ^ N * (wb ^ N * (1 + v) ^ N)
      = (1 + u) ^ N * (1 + v) ^ N * (wa ^ N * wb ^ N) := by ring
    _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) * (wa ^ N * wb ^ N) := mul_le_mul_of_nonneg_right key hw

theorem Nexp_le (N Y La : ℝ) (hN : 2 ≤ N) (hY : 1 ≤ Y) (hLa : 8 * Real.log (N * Y) ≤ La) :
    N * Real.exp (-La / 3) ≤ 0.36 := by
  have hNY : 2 ≤ N * Y := by nlinarith
  have hL2 : Real.log 2 ≤ Real.log (N * Y) := Real.log_le_log (by norm_num) hNY
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (N * Y) with hL
  have hexpL : Real.exp L = N * Y := Real.exp_log (by linarith)
  have h1 : N ^ 2 ≤ Real.exp (2 * L) := by
    have hNY1 : N ≤ N * Y := by nlinarith
    rw [show 2 * L = L + L by ring, Real.exp_add, hexpL, sq]
    exact mul_le_mul hNY1 hNY1 (by linarith) (by linarith)
  have h2 : 1 + 2 * L / 3 ≤ Real.exp (2 * L / 3) := by linarith [Real.add_one_le_exp (2 * L / 3)]
  have h3 : Real.exp (2 * L) * Real.exp (2 * L / 3) ≤ Real.exp (La / 3) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h4 : N ^ 2 * (1 + 2 * L / 3) ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le) h3
  have h5 : N ^ 2 * 1.46 ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg N)) h4
  have hpos : 0 < Real.exp (La / 3) := Real.exp_pos _
  rw [show -La / 3 = -(La / 3) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def Cst.TM2 (K : Cst) : ℝ := max K.TLP 400

theorem div_small (x w Yb c : ℝ) (hw : 0 < w) (hYb : 400 ≤ Yb) (h : x * Yb ≤ c * w) : x / w ≤ c / Yb := by
  rw [div_le_div_iff₀ hw (by linarith)]
  linarith

set_option maxHeartbeats 1600000 in
theorem threshold_density_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => DensityNumericalFacts K) := by
  refine ⟨K.TM2, 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), one_pos, fun CH hCH _ _ X h => ?_⟩
  have hTLP : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h400 : (400 : ℝ) ≤ CH := le_trans (le_max_right _ _) hCH
  have B := base_of K hK CH hTLP X h
  have Wf := winFacts_of K hK CH hTLP X h
  obtain ⟨l1, l2, -⟩ := La_round hK B
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  have hYb400 : (400 : ℝ) ≤ X.Yb := le_trans h400 hYb
  have hN2 : (2 : ℝ) ≤ (X.N : ℝ) := B.hN2
  have hN0 : (0 : ℝ) < (X.N : ℝ) := by linarith
  have hk5 : (5 : ℝ) ≤ X.k := B.hk5
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have h200 := two_hundred_le_radius B
  have ha200 : (200 : ℝ) ≤ X.a := le_trans h200 B.haa
  obtain ⟨La, hLa⟩ : ∃ La, La = LaI K.C₀ X.N₁ X.ar := ⟨_, rfl⟩
  obtain ⟨La', hLa'⟩ : ∃ La', La' = LaI K.C₀ X.N₁ (X.a : ℝ) := ⟨_, rfl⟩
  rw [← hLa] at hLa1 l1 l2 hccl hkLa hab hLa8
  rw [← hLa'] at l1 l2
  have hwa := Wf.wa_ge
  have hwb := Wf.wb_ge
  rw [← hLa] at hwa hwb
  have hJ0 : X.J0 K = La' * X.b' / X.k := by rw [hLa']; rfl
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = La * X.b' / X.k := ⟨_, rfl⟩
  have hZk : Z * X.k = La * X.b' := by rw [hZ]; exact div_mul_cancel₀ _ hk0.ne'
  have hcclZ : (X.ccl : ℝ) ≤ Z := by rw [hZ]; exact hccl
  have hJ0Z : X.J0 K ≤ 2 * Z := by
    rw [hJ0, hZ]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l2 hb.le) hk0.le
    calc La' * X.b' / X.k ≤ 2 * La * X.b' / X.k := this
      _ = _ := by ring
  have hLa'0 : 0 ≤ La' := by linarith
  have hJ00 : 0 ≤ X.J0 K := by rw [hJ0]; positivity

  have hkLa' : CH * (X.N : ℝ) * La ^ 2 ≤ X.k := hkLa
  have hLaLa : La ≤ La ^ 2 := le_self_pow₀ hLa1 (by norm_num)
  have hCHN : 0 ≤ CH * (X.N : ℝ) := by positivity
  have hkbig : CH * (X.N : ℝ) * La ≤ X.k := le_trans (mul_le_mul_of_nonneg_left hLaLa hCHN) hkLa'
  have hk800 : (800 : ℝ) ≤ X.k := by
    have a1 : (400 : ℝ) * 2 * 1 ≤ CH * (X.N : ℝ) * La := by gcongr
    linarith
  have hm5 : 5 ≤ X.m := by
    have : (5 : ℝ) ≤ (X.m : ℝ) := by
      have : X.k = (X.m : ℝ) + 1 := rfl
      linarith
    exact_mod_cast this

  have hZb : CH * (X.N : ℝ) * Z ≤ X.b' := by
    have a1 : CH * (X.N : ℝ) * La * X.b' ≤ X.k * X.b' := mul_le_mul_of_nonneg_right hkbig hb.le
    have a2 : CH * (X.N : ℝ) * Z * X.k ≤ X.b' * X.k := by
      calc CH * (X.N : ℝ) * Z * X.k = CH * (X.N : ℝ) * (Z * X.k) := by ring
        _ = CH * (X.N : ℝ) * La * X.b' := by rw [hZk]; ring
        _ ≤ X.k * X.b' := a1
        _ = _ := by ring
    exact le_of_mul_le_mul_right a2 hk0
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hZ800 : 800 * Z ≤ X.b' := by
    have : (400 : ℝ) * 2 * Z ≤ CH * (X.N : ℝ) * Z := by gcongr
    linarith
  have hkb : CH * X.k * 8 ≤ X.b' := B.hsz X.k 8 hk0.le (k_le_G B) (by norm_num) (by
    have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.ccl := by positivity
    have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
    have h3 : (8 : ℝ) ≤ X.cStar := by
      have : 8 ≤ X.cStar := by omega
      exact_mod_cast this
    linarith)
  have hkb' : 3200 * X.k ≤ X.b' := by
    have : (400 : ℝ) * X.k * 8 ≤ CH * X.k * 8 := by gcongr
    linarith
  have hZ1 : 1 ≤ Z := by
    have a1 : 1 * X.k ≤ Z * X.k := by
      rw [hZk]
      have : 1 * X.b' ≤ La * X.b' := mul_le_mul_of_nonneg_right hLa1 hb.le
      linarith
    exact le_of_mul_le_mul_right a1 hk0

  have hYNZ : 800 ≤ X.Yb * (X.N : ℝ) * Z := by
    have : (400 : ℝ) * 2 * 1 ≤ X.Yb * (X.N : ℝ) * Z := by gcongr
    linarith
  have hwb2 : X.Yb * (X.N : ℝ) * Z / 2 ≤ ((X.Wb 0).card : ℝ) := by
    have : X.Yb * (X.N : ℝ) * La * X.b' / X.k = X.Yb * (X.N : ℝ) * Z := by rw [hZ]; ring
    rw [this] at hwb
    linarith
  have hwa2 : X.Yb * (X.N : ℝ) * Z / 2 ≤ ((X.Wa 0).card : ℝ) := by
    have e1 : X.Yb * (X.N : ℝ) * La * X.b' = X.Yb * (X.N : ℝ) * Z * X.k := by
      rw [mul_assoc (X.Yb * (X.N : ℝ)) Z, hZk]; ring
    have e2 : X.Yb * (X.N : ℝ) * Z * 1 ≤ X.Yb * (X.N : ℝ) * Z * X.k :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [e1] at hwa
    linarith
  have hwaR : (0 : ℝ) < ((X.Wa 0).card : ℝ) := by linarith
  have hwbR : (0 : ℝ) < ((X.Wb 0).card : ℝ) := by linarith
  have hwaN : 0 < (X.Wa 0).card := by exact_mod_cast hwaR
  have hwbN : 0 < (X.Wb 0).card := by exact_mod_cast hwbR
  have cA : (X.WaP K).card = (X.Wa 0).card + (X.Jn K + X.ccl) := by
    have := card_first_window X
    simp only [Dat.WaP, Nat.card_Icc]
    omega
  have cB : (X.WbP K).card = (X.Wb 0).card + (X.Jn K + X.ccl) := by
    have := card_second_window X
    simp only [Dat.WbP, Nat.card_Icc]
    omega
  have hJn : (X.Jn K : ℝ) ≤ X.J0 K := Nat.floor_le hJ00
  have he3 : ((X.Jn K + X.ccl : ℕ) : ℝ) ≤ 3 * Z := by
    push_cast
    linarith
  have he0 : (0 : ℝ) ≤ ((X.Jn K + X.ccl : ℕ) : ℝ) := Nat.cast_nonneg _

  have hmk : (X.m : ℝ) ≤ X.k := by
    have : X.k = (X.m : ℝ) + 1 := rfl
    linarith
  have hmJ : (X.m : ℝ) * X.J0 K ≤ 2 * (La * X.b') := by
    have a1 : (X.m : ℝ) * X.J0 K ≤ X.k * X.J0 K := mul_le_mul_of_nonneg_right hmk hJ00
    have a2 : X.k * X.J0 K ≤ X.k * (2 * Z) := mul_le_mul_of_nonneg_left hJ0Z hk0.le
    have a3 : X.k * (2 * Z) = 2 * (La * X.b') := by rw [← hZk]; ring
    linarith
  have hG : X.Yb * (X.N : ℝ) * (La * X.b') ≤ X.a := by
    rw [le_div_iff₀ hb] at hab
    have hnn : 0 ≤ X.Yb * (X.N : ℝ) * (La * X.b') := by positivity
    have h1 : (1 : ℝ) ≤ X.k * X.Y ^ 2 * Real.log X.ar :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hY)) B.hlog1
    have h2 := mul_le_mul_of_nonneg_left h1 hnn
    have h3 : X.Yb * (X.N : ℝ) * (La * X.b') * (X.k * X.Y ^ 2 * Real.log X.ar) =
        ((X.m : ℝ) + 1) * X.Y ^ 2 * X.Yb * X.TT.card * La * Real.log X.ar * X.b' := by
      unfold Dat.k Dat.N; ring
    linarith [B.haa]
  have hmJ0 : 0 ≤ (X.m : ℝ) * X.J0 K := by positivity
  have ha0 : (0 : ℝ) < X.a := by linarith
  have hx1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) ≤ 0.005 := by
    have a1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) / X.a ≤ 2 / X.Yb := by
      apply div_small _ _ _ _ ha0 hYb400
      have b1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) * X.Yb ≤ (X.N : ℝ) * (2 * (La * X.b')) * X.Yb := by gcongr
      linarith
    have a2 : 2 / X.Yb ≤ 0.005 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) = (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) / X.a := by ring
      _ ≤ 0.005 := le_trans a1 a2
  have hx2 : (X.N : ℝ) * Real.exp (-La' / 3) ≤ 0.36 := by
    have a1 : Real.exp (-La' / 3) ≤ Real.exp (-La / 3) := Real.exp_le_exp.2 (by linarith)
    have a2 := Nexp_le (X.N : ℝ) X.Y La hN2 hY hLa8
    have a3 := mul_le_mul_of_nonneg_left a1 hN0.le
    linarith
  have h6 : 6 / X.Yb ≤ 0.015 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hx3 : (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ)) ≤ 0.015 := by
    have a1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) ≤ 6 / X.Yb := by
      apply div_small _ _ _ _ hwaR hYb400
      have b1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) * X.Yb ≤ (X.N : ℝ) * (3 * Z) * X.Yb := by gcongr
      linarith
    calc _ = (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) := by ring
      _ ≤ 0.015 := le_trans a1 h6
  have hx4 : (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) ≤ 0.015 := by
    have a1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ) ≤ 6 / X.Yb := by
      apply div_small _ _ _ _ hwbR hYb400
      have b1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) * X.Yb ≤ (X.N : ℝ) * (3 * Z) * X.Yb := by gcongr
      linarith
    calc _ = (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ) := by ring
      _ ≤ 0.015 := le_trans a1 h6
  have hx10 : 0 ≤ (X.m : ℝ) * X.J0 K / X.a := by positivity
  have hx11 : (X.m : ℝ) * X.J0 K / X.a ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (X.N : ℝ)) hx10
    linarith
  have hx20 : 0 ≤ Real.exp (-La' / 3) := (Real.exp_pos _).le
  have hx21 : Real.exp (-La' / 3) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hN1n : 1 ≤ X.N := by
    have : (1 : ℝ) ≤ (X.N : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨by omega, ⟨by omega, by omega⟩,
    (1 - (X.m : ℝ) * X.J0 K / X.a) * (1 - Real.exp (-La' / 3)), mul_nonneg (by linarith) (by linarith), ?_, ?_⟩
  · intro τ hτ al hal be hbe
    obtain ⟨hal1, -⟩ := Finset.mem_Icc.1 hal
    obtain ⟨-, hbe2⟩ := Finset.mem_Icc.1 hbe
    have hala : (X.a : ℝ) ≤ al := by
      have : X.a ≤ al := by omega
      exact_mod_cast this
    have hal0 : 0 < al := by
      have : (0 : ℝ) < al := by linarith
      exact_mod_cast this
    have hbeR : (be : ℝ) ≤ X.bu + Z := by
      have a1 : (be : ℝ) ≤ (X.ub : ℝ) + τ := by exact_mod_cast hbe2
      have a2 : (X.ub : ℝ) ≤ X.bu := Nat.floor_le Wf.bunn
      have a3 : (τ : ℝ) ≤ X.ccl := by exact_mod_cast hτ
      linarith
    have hcond : (be : ℝ) + ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ) + (X.m : ℝ) + 1 ≤ 2 * X.b' := by
      have a1 : ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ : ℕ) : ℝ) ≤ 2 * Z := by
        have : ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ : ℕ) : ℝ) = (X.Jn K : ℝ) := by
          unfold Dat.Jn
          rw [hJ0]
          rfl
        rw [this]
        linarith
      push_cast
      have := Wf.bule
      linarith
    have key := Formalism.CountingSumsFrames.Top.densityLower X.m al be La' X.b' hm5 hal0 hb hLa'0 hcond
    have e1 : (X.m : ℝ) * (La' * X.b' / ((X.m : ℝ) + 1)) = (X.m : ℝ) * X.J0 K := by rw [hJ0]; rfl
    have e2 : ⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ = X.Jn K := by
      unfold Dat.Jn
      rw [hJ0]
      rfl
    rw [e1, e2] at key
    refine le_trans ?_ key
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : (X.m : ℝ) * X.J0 K / al ≤ (X.m : ℝ) * X.J0 K / X.a := div_le_div_of_nonneg_left hmJ0 ha0 hala
    linarith
  · rw [cA, cB]
    push_cast
    have := dens_abs X.N hN1n ((X.m : ℝ) * X.J0 K / X.a) (Real.exp (-La' / 3)) ((X.Wa 0).card : ℝ)
      ((X.Wb 0).card : ℝ) ((X.Jn K + X.ccl : ℕ) : ℝ) hx10 hx20 hwaR hwbR he0 (by
        have e : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a + Real.exp (-La' / 3) +
            ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) + ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) =
            (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) + (X.N : ℝ) * Real.exp (-La' / 3) +
            (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ)) +
            (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) := by ring
        rw [e]
        linarith)
    push_cast at this
    exact this

end Formalism.MainNotions.flipOneThree.Pf

end
