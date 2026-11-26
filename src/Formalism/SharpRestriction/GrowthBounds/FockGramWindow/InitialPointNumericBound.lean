module

public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LvlDef
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfMinimalVector

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FockKSmulRight
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

end Formalism.MainNotions.G.SymmetricFormBlocks

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem winA_sum (X : flipOneThree.Inst) (f : ℕ → ℝ) :
    ∑ aPlus ∈ X.winA, f aPlus = ∑ j ∈ Finset.range X.winA.card, f (X.L.a + j) := by
  unfold flipOneThree.Inst.winA
  rw [Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.FirstCoefficientLeDiv
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.RestWinOfLvl
noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestWinNum (CM : ℝ) : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ J : ℕ,
    J ≤ (X.S C0 CE1 CE2).bPlus →
    b.oPlus ≤ X.L.a ∧ 0 ≤ X.L.Y * D1r C0 CE1 CE2 X CM ∧
    ∃ h : ℕ, X.winA.card ≤ X.p ^ h ∧ J + 1 ≤ X.p ^ h ∧
      (J : ℝ) / X.winA.card +
        (((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) + lgN X.p (aBig X) X.r) +
          (J : ℝ) * h / X.winA.card) / (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) ≤ 5 / X.L.Y

variable {C0 CE1 CE2 X}

theorem restWin_of_lvl {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (CM : ℝ) (hL : WinLvl) (hN : RestWinNum C0 CE1 CE2 X CM)
    (haw : X.L.a ∈ X.winA) :
    RestWin C0 CE1 CE2 X CM := by
  classical
  haveI : NeZero X.r := ⟨X.hm⟩
  intro dl hdl aTop haTop x hx n₁ e he hli horth hdiag
  have haTop' : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) := by
    unfold cbox at haTop
    exact (Finset.mem_filter.mp haTop).1
  unfold idx at hx
  rw [Finset.mem_sigma] at hx
  have hK : Kept X.p X.r (X.S C0 CE1 CE2) aTop x.fst :=
    (mem_keptSet _ _ _ _ _).mp (Finset.mem_filter.mp hx.1).1
  have hlv : x.snd ∈ levels (gB C0 CE1 CE2 X aTop 0 x.fst) := hx.2
  unfold levels at hlv
  have hLOK : (gB C0 CE1 CE2 X aTop 0 x.fst).LevelOK x.snd.1 x.snd.2 :=
    (Finset.mem_filter.mp hlv).2
  have hJ : JN (gB C0 CE1 CE2 X aTop 0 x.fst) x.snd.2 ≤ (X.S C0 CE1 CE2).bPlus :=
    le_trans (min_le_right _ _) (Nat.sub_le _ _)
  obtain ⟨hob, hYD, h, hWh, hJh, hineq⟩ := hN aTop haTop' x.fst hK _ hJ
  obtain ⟨hA1, hdeg, hB, hz, -⟩ :=
    gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop haTop' X.L.a haw x.fst hK
  have hW : 0 < X.winA.card := Finset.card_pos.mpr ⟨_, haw⟩
  have hk : 0 ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.mpr hYD
  have hmain := hL X.p (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.fst) (gB_blockOK _ _ _ _ _ _ _)
    x.snd.1 x.snd.2 hLOK (aBig X) hA1 hdeg hB hz n₁ e he hli horth ⌊D1r C0 CE1 CE2 X CM⌋ hdiag
    (X.L.a - x.fst.oPlus) X.winA.card h _ hk hW hWh hJh
  have hbe : ∀ (aPlus z : ℕ), aPlus - x.fst.oPlus = z →
      bejj (r := X.r) X.p (gB C0 CE1 CE2 X aTop aPlus x.fst) x.snd.1 x.snd.2 =
        bejj (r := X.r) X.p (setZ (gB C0 CE1 CE2 X aTop 0 x.fst) z) x.snd.1 x.snd.2 := by
    rintro aPlus z rfl
    rfl
  rw [winA_sum]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) (le_trans hmain ?_)
  · rw [hbe (X.L.a + i) (X.L.a - x.fst.oPlus + i) (by omega)]
    rfl
  · rw [mul_comm (5 / X.L.Y)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left hineq (Nat.cast_nonneg _)

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem segG_pos {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : 1 ≤ segG TT j := by
  unfold segG
  split_ifs with h
  · exact (segStart TT j).pos
  · exact Nat.one_le_iff_ne_zero.mpr h

theorem cap_le' {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B) (l : ℕ) :
    (cap p S b l : ℝ) ≤ S.A0 p + s * B := by
  unfold cap
  push_cast
  refine add_le_add le_rfl ((Finset.sum_le_card_nsmul _ _ B ?_).trans ?_)
  · intro i _
    have hc : coarseA p S b i ≤ S.bTop i := by
      unfold coarseA
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hcR : (coarseA p S b i : ℝ) ≤ B := (Nat.cast_le.mpr hc).trans (hB i)
    have h0 : (0 : ℝ) ≤ B := (Nat.cast_nonneg _).trans (hB i)
    have hoe : (0 : ℝ) ≤ (oEff S b i : ℝ) := Nat.cast_nonneg _
    split_ifs <;> linarith
  · simp

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem first_coefficient_le_div : (((X.S C0 CE1 CE2).A0 X.p : ℤ) : ℝ) ≤ X.L.a / 25 := by
  unfold SegData.A0
  refine (Int.floor_le _).trans ?_
  have hp25 := p25 hS.hF
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hQ : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := by
    show (X.p : ℝ) ≤ ((X.p ^ segG X.L.TT X.j : ℕ) : ℝ)
    have : X.p ^ 1 ≤ X.p ^ segG X.L.TT X.j := Nat.pow_le_pow_right hp1 (segG_pos _ _)
    rw [pow_one] at this
    exact_mod_cast this
  have hQ25 : (25 : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := hp25.trans hQ
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hE := hS.E0
  have ha : (((X.S C0 CE1 CE2).a : ℕ) : ℝ) = X.L.a := rfl
  rw [ha, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

private theorem geo_lemma (n : ℕ) (p : ℝ) (hp : 1 < p) (f : Fin n → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∀ i, f i ≤ 1) (hs : ∀ i j : Fin n, i < j → p * f i ≤ f j) : ∑ i, f i ≤ p / (p - 1) := by
  cases n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg (by linarith) (by linarith)
  | succ n =>
    have hA := Fin.sum_univ_castSucc f
    have hB := Fin.sum_univ_succ f
    have hC : ∑ i : Fin n, p * f i.castSucc ≤ ∑ i : Fin n, f i.succ :=
      Finset.sum_le_sum (fun i _ => hs _ _ Fin.castSucc_lt_succ)
    rw [← Finset.mul_sum] at hC
    have hf0 := h0 0
    have hfl := h1 (Fin.last n)
    rw [le_div_iff₀ (by linarith)]
    nlinarith

theorem oplus_le_a (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    b.oPlus ≤ X.L.a := by
  have hF := hS.hF
  have hK4 := hK.2.2.2
  unfold Oplus at hK4
  have hcap := cap_le' (p := X.p) (X.S C0 CE1 CE2) b (5 / 2 * X.L.b') hS.bTop X.s
  have hA0 := first_coefficient_le_div hS
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpg := hF.p_ge
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith
  have hb0 := hF.b0
  have hkb : ((X.L.m : ℝ) + 1) * X.L.b' ≤ X.L.a / 4 := hS.kb
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hsb : (X.s : ℝ) * X.L.b' ≤ X.L.a / 8 := by nlinarith
  have hLa0 : 0 ≤ X.L.La C0 := hF.La0
  have hLa4 : 4 * X.L.La C0 < (X.L.m : ℝ) + 1 := hS.La4
  have hc1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hq : 4 / (X.L.p : ℝ) ^ 2 ≤ 4 / 625 := by
    gcongr
    nlinarith
  have hq0 : 0 ≤ 4 / (X.L.p : ℝ) ^ 2 := by positivity
  have hPpos : ∀ i, (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := fun i => by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X i
  have hg := geo_lemma hS X.s (X.L.p : ℝ) (by linarith)
    (fun i => 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)) (fun i => (one_div_pos.mpr (hPpos i)).le)
    (fun i => by
      have := hS.P1 i
      rw [div_le_one (hPpos i)]
      exact_mod_cast this)
    (fun i j hij => by
      have h1 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) i j hij
      have h1' : (X.L.p : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) j : ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
        exact_mod_cast h1
      rw [mul_one_div, div_le_div_iff₀ (hPpos i) (hPpos j)]
      linarith)
  have hgeo : (X.L.p : ℝ) / ((X.L.p : ℝ) - 1) ≤ 25 / 24 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hTe : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      = 2 * (X.L.a : ℝ) * ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hT0 : 0 ≤ ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) :=
    Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hPpos i)).le)
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hT : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ 2 * X.L.a * (25 / 24) := by
    rw [hTe]
    exact mul_le_mul_of_nonneg_left (hg.trans hgeo) (by positivity)
  have hT0' : 0 ≤ ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [hTe]
    positivity
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hF.bT_le _ hmem
  have hbP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
  have hLb : X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1)
      ≤ 1 / 4 * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hc1 hbP0
  have hcT : (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
      * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      ≤ (1 / 4 + 4 / 625) * (2 * X.L.a * (25 / 24)) :=
    mul_le_mul (by linarith) hT hT0' (by norm_num)
  have hK5 : (b.oPlus : ℝ) ≤ ((cap X.p (X.S C0 CE1 CE2) b X.s : ℤ) : ℝ)
      + (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
        * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      + X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1) := hK4
  have hfin : (b.oPlus : ℝ) ≤ X.L.a := by nlinarith
  exact_mod_cast hfin

theorem a_mem_win : X.L.a ∈ X.winA := by
  unfold flipOneThree.Inst.winA
  rw [Finset.mem_Icc]
  refine ⟨le_rfl, Nat.le_floor ?_⟩
  have h1 : (0 : ℝ) ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y) := by
    have hk : (0 : ℝ) ≤ X.L.k := by
      show (0 : ℝ) ≤ (X.L.m : ℝ) + 1
      positivity
    have := hS.Y1
    positivity
  linarith [hS.xa0]

end Deg

theorem eps_num (Y D1 κ q h x0l fl E : ℝ) (hY : 1 ≤ Y) (hκ : 0 < κ) (hD : κ ≤ D1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / (2 * Y))
    (hh0 : 0 ≤ h) (hh : h ≤ κ) (hx : x0l ≤ κ) (hfl : fl ≤ D1) (hE : Y * D1 ≤ E) :
    q + (x0l + fl + q * h) / E ≤ 5 / Y := by
  have hD1 : 0 < D1 := lt_of_lt_of_le hκ hD
  have hY0 : 0 < Y := by linarith
  have hYD : 0 < Y * D1 := mul_pos hY0 hD1
  have hE0 : 0 < E := lt_of_lt_of_le hYD hE
  have hq1 : q ≤ 1 := by
    have : 1 / (2 * Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hqh : q * h ≤ D1 := by nlinarith [mul_le_mul_of_nonneg_right hq1 hh0]
  have hnum : x0l + fl + q * h ≤ 3 * D1 := by linarith
  have h1 : (x0l + fl + q * h) / E ≤ 3 / Y := by
    rw [div_le_div_iff₀ hE0 hY0]
    nlinarith [mul_le_mul_of_nonneg_right hnum hY0.le]
  have h2 : q ≤ 1 / Y := by
    have : 1 / (2 * Y) ≤ 1 / Y := by
      gcongr
      linarith
    linarith
  have h3 : 1 / Y + 3 / Y ≤ 5 / Y := by
    rw [← add_div]
    gcongr
    norm_num
  linarith

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem clog_le_lg (p : ℕ) (hp : 1 < p) (x : ℕ) (hx : 2 ≤ x) : (Nat.clog p x : ℝ) ≤ Real.logb p x + 1 := by
  have hpos : 0 < Nat.clog p x := Nat.clog_pos hp (by omega)
  have hk := Nat.pow_pred_clog_lt_self p (by omega : 1 < x)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hxR : (0 : ℝ) < x := by positivity
  have h1 : (p : ℝ) ^ (Nat.clog p x).pred < x := by exact_mod_cast hk
  have h2 : ((Nat.clog p x).pred : ℝ) < Real.logb p x := by
    rw [Real.lt_logb_iff_rpow_lt hpR hxR, Real.rpow_natCast]
    exact h1
  have h3 : Nat.clog p x = (Nat.clog p x).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [h3]
  push_cast
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

private theorem twentyfive_le_p_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : (25 : ℝ) ≤ X.L.p := by
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hS.hF.m4
  nlinarith [hS.hF.p_ge]

theorem lgN_le (hS : SegFacts C0 CE1 CE2 X) : (lgN X.p (aBig X) X.r : ℝ) ≤ lgA X.p X.L.a X.r + 1 := by
  have hF := hS.hF
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hyN : 8 * aBig X + X.r ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    unfold aBig
    have := Nat.mul_pos (by omega : 0 < 3 * X.s + 2) (by omega : 0 < X.L.a)
    omega
  have hpow := Nat.pow_log_le_self X.p hyN
  have hyR : (0 : ℝ) < ((8 * aBig X + X.r : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hyN
  have hlog : ((Nat.log X.p (8 * aBig X + X.r) : ℕ) : ℝ) ≤ Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le hp1 hyR, Real.rpow_natCast]
    exact_mod_cast hpow
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hyle : ((8 * aBig X + X.r : ℕ) : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r) := by
    unfold aBig
    push_cast
    nlinarith
  have hA : (0 : ℝ) < 8 * X.L.a + X.r := by linarith
  have hB : (0 : ℝ) < 3 * (X.s : ℝ) + 2 := by linarith
  have h2 : Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ)
      ≤ Real.logb X.p ((3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r)) :=
    Real.logb_le_logb_of_le hp1 hyR hyle
  rw [Real.logb_mul hB.ne' hA.ne'] at h2
  have h3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow hp1 hB, Real.rpow_one]
    show 3 * (X.s : ℝ) + 2 ≤ X.L.p
    nlinarith [hF.p_ge]
  unfold lgN lgA
  push_cast
  linarith

theorem initial_point_numeric_bound (t s r L lam : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr4 : 4 ≤ r) (hL : L ≤ 2 * lam)
    (hlam : 0 ≤ lam) : ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2)) * L + L ≤ 3 * (s + 2) * r ^ 2 * lam := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hC0 : 0 ≤ (t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1 := by nlinarith
  have key := mul_le_mul_of_nonneg_left hL hC0
  have hcoef : 2 * ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1) ≤ 3 * (s + 2) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hts (by linarith : (0 : ℝ) ≤ r),
      mul_le_mul_of_nonneg_left hr4 (by nlinarith : (0 : ℝ) ≤ (s + 2) * r)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hlam]

theorem initial_point_nat_cast (p A r N t : ℕ) : (x0N p A r N t : ℝ) =
    (((t : ℝ) + 1) * ((r : ℝ) + 1) + (((N : ℝ) + 1) * (r : ℝ) + ((t : ℝ) + 1) * 2)) * (lgN p A r : ℝ) := by
  unfold x0N; push_cast; ring

private theorem one_le_lgA_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : 1 ≤ lgA X.p X.L.a X.r := by
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hS.hF.a1
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  unfold lgA
  have : 0 ≤ Real.logb X.p (8 * X.L.a + X.r) := Real.logb_nonneg hp1 (by linarith)
  linarith

theorem hx_inst (hS : SegFacts C0 CE1 CE2 X) :
    (x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + lgN X.p (aBig X) X.r ≤ kapS X := by
  have hF := hS.hF
  rw [initial_point_nat_cast]
  push_cast
  have hL := lgN_le hS
  have hlam1 := one_le_lgA_of_segFacts hS
  have htN : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ X.s := by exact_mod_cast htN
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have key := initial_point_numeric_bound ((X.S C0 CE1 CE2).t : ℝ) X.s X.r (lgN X.p (aBig X) X.r) (lgA X.p X.L.a X.r)
    (Nat.cast_nonneg _) ht hr4 (by linarith) (by linarith)
  unfold kapS
  linarith

theorem win_facts (hS : SegFacts C0 CE1 CE2 X) :
    (X.L.a : ℝ) / (X.L.k * X.L.Y) ≤ (X.winA.card : ℝ) ∧ X.winA.card ≤ X.L.a + 1 := by
  have hF := hS.hF
  have hmem := a_mem_win hS
  unfold flipOneThree.Inst.winA at hmem ⊢
  rw [Nat.card_Icc]
  have haF := (Finset.mem_Icc.mp hmem).2
  have hlt := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
  have hle : ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) ≤ 2 * X.L.a :=
    (Nat.floor_le hF.win0).trans hF.win_le
  have hleN : ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ ≤ 2 * X.L.a := by exact_mod_cast hle
  constructor
  · rw [Nat.cast_sub (by omega)]
    push_cast
    linarith [hS.xa0]
  · omega

theorem q_num (J W a k Y b' p : ℝ) (hY : 1 ≤ Y) (hk : 5 ≤ k) (hb : 0 < b') (hpk : k ^ 2 * Y ^ 2 ≤ p) (hpb : p * b' < a)
    (hJ : J ≤ 5 / 2 * b') (hW : a / (k * Y) ≤ W) : 0 < W ∧ J / W ≤ 1 / (2 * Y) := by
  have hY0 : 0 < Y := by linarith
  have hk0 : 0 < k := by linarith
  have hkY : 0 < k * Y := mul_pos hk0 hY0
  have hp0 : 0 < p := by
    have : 0 < k ^ 2 * Y ^ 2 := by positivity
    linarith
  have ha0 : 0 < a := by
    have := mul_pos hp0 hb
    linarith
  have hW1 : k * Y * b' < a / (k * Y) := by
    rw [lt_div_iff₀ hkY]
    have e : k * Y * b' * (k * Y) = k ^ 2 * Y ^ 2 * b' := by ring
    rw [e]
    have : k ^ 2 * Y ^ 2 * b' ≤ p * b' := mul_le_mul_of_nonneg_right hpk hb.le
    linarith
  have hkYb : 0 < k * Y * b' := by positivity
  have hW0 : 0 < W := by linarith
  refine ⟨hW0, ?_⟩
  rw [div_le_div_iff₀ hW0 (by positivity)]
  have h1 : J * (2 * Y) ≤ 5 * b' * Y := by
    nlinarith [mul_le_mul_of_nonneg_right hJ (by linarith : (0 : ℝ) ≤ 2 * Y)]
  have h2 : 5 * b' * Y ≤ k * Y * b' := by
    nlinarith [mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ Y * b')]
  linarith

theorem kap_facts (hS : SegFacts C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) :
    lgA X.p X.L.a X.r ≤ kapS X ∧ 0 < kapS X ∧ kapS X ≤ D1r C0 CE1 CE2 X CM := by
  have hF := hS.hF
  have hlam1 := one_le_lgA_of_segFacts hS
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hc : 1 ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith
  have hk : lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    nlinarith
  have hk0 : 0 < kapS X := by linarith
  refine ⟨hk, hk0, ?_⟩
  unfold D1r
  have ht0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have hY := hS.Y1
  have h1 : 0 ≤ X.L.Y * kapS X + CM * kapS X := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < X.L.Y) hk0, mul_pos (by linarith : (0 : ℝ) < CM) hk0]
  nlinarith [mul_nonneg ht0 h1, mul_le_mul_of_nonneg_right hCM hk0.le]

private theorem bPlus_le_five_halves_mul_b' (hS : SegFacts C0 CE1 CE2 X) :
    ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := by
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  exact hS.hF.bT_le _ hmem

theorem restWinNum_proved (hS : SegFacts C0 CE1 CE2 X) (hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ)) (CM : ℝ)
    (hCM : 1 ≤ CM) : RestWinNum C0 CE1 CE2 X CM := by
  intro aTop haTop b hK J hJ
  have hF := hS.hF
  have hY1 := hS.Y1
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have hp1N : 1 < X.p := by exact_mod_cast hp1
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hk5 : (5 : ℝ) ≤ X.L.k := by
    unfold ColumnSystems.Loc.k
    linarith
  obtain ⟨hlk, hk0, hkD⟩ := kap_facts hS CM hCM
  have hD0 : 0 < D1r C0 CE1 CE2 X CM := lt_of_lt_of_le hk0 hkD
  refine ⟨oplus_le_a hS b aTop hK, mul_nonneg (by linarith) hD0.le, ?_⟩
  obtain ⟨hWlow, hWup⟩ := win_facts hS
  have hJR : (J : ℝ) ≤ 5 / 2 * X.L.b' := (Nat.cast_le.mpr hJ).trans (bPlus_le_five_halves_mul_b' hS)
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have hJa : (J : ℝ) ≤ X.L.a := by nlinarith
  have hJaN : J + 1 ≤ X.L.a + 1 := by
    have : J ≤ X.L.a := by exact_mod_cast hJa
    omega
  refine ⟨Nat.clog X.p (X.L.a + 1), hWup.trans (Nat.le_pow_clog hp1N _),
    hJaN.trans (Nat.le_pow_clog hp1N _), ?_⟩
  obtain ⟨hW0, hqY⟩ := q_num (J : ℝ) (X.winA.card : ℝ) X.L.a X.L.k X.L.Y X.L.b' X.L.p hY1 hk5 hb0 hpk hblt hJR hWlow
  have hq0 : 0 ≤ (J : ℝ) / (X.winA.card : ℝ) := div_nonneg (Nat.cast_nonneg _) hW0.le
  have hh0 : (0 : ℝ) ≤ (Nat.clog X.p (X.L.a + 1) : ℝ) := Nat.cast_nonneg _
  have hhk : (Nat.clog X.p (X.L.a + 1) : ℝ) ≤ kapS X := by
    have h1 := clog_le_lg X.p hp1N (X.L.a + 1) (by omega)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    have hlog : Real.logb X.p ((X.L.a + 1 : ℕ) : ℝ) ≤ Real.logb X.p (8 * X.L.a + X.r) :=
      Real.logb_le_logb_of_le hp1 (by positivity) (by push_cast; linarith)
    unfold lgA at hlk
    linarith
  have hx := hx_inst hS
  have hfl : ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) ≤ D1r C0 CE1 CE2 X CM := Int.floor_le _
  have hE : X.L.Y * D1r C0 CE1 CE2 X CM ≤ ((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1 :=
    (Int.lt_floor_add_one _).le
  have key := eps_num X.L.Y (D1r C0 CE1 CE2 X CM) (kapS X) ((J : ℝ) / (X.winA.card : ℝ))
    (Nat.clog X.p (X.L.a + 1) : ℝ)
    ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ))
    ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1)
    hY1 hk0 hkD hq0 hqY hh0 hhk hx hfl hE
  calc _ = (J : ℝ) / (X.winA.card : ℝ)
        + ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ)
          + ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + (J : ℝ) / (X.winA.card : ℝ) * (Nat.clog X.p (X.L.a + 1) : ℝ))
          / (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) := by ring
    _ ≤ 5 / X.L.Y := key

end Formalism.MainNotions.G.GramWindowAlt

end
