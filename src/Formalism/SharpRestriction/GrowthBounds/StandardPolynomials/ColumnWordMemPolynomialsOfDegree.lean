module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultMk

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SymFamilyWordEqHeadMulMonomial
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialWeightedHomogeneous
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NdHomSingle
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.StdPolyEq
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ThresholdStandardSeventeen
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem error_exponent_lower_bound {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2) (hc : 1 ≤ X.c) :
    localOrderCap C0 X + (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ X.E0 C0 CE1 CE2 := by
  have hp5 : (5 : ℝ) ≤ X.p := by exact_mod_cast St.p5
  have hp : (0 : ℝ) < X.p := by linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk : (1 : ℝ) ≤ X.k := by have := St.N1k; linarith
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hQ : (1 : ℝ) ≤ X.Q := one_le_pow₀ (by linarith)
  have hcr : (1 : ℝ) ≤ X.c := by exact_mod_cast hc
  have hLa : (0 : ℝ) ≤ X.La C0 := by have := St.La1; linarith
  have ha : (0 : ℝ) ≤ X.a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ X.b' := St.bpos.le
  have A1 : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 := by positivity
  have B1 : 0 ≤ X.b' / (X.p : ℝ) := by positivity
  have L0 : 0 ≤ X.La C0 * X.a / (X.p * X.k) := by positivity
  have L2 : 0 ≤ X.La C0 * X.b' / X.k := by positivity
  have e1 : X.La C0 * X.N1 * X.a / (X.p * X.k) = X.N1 * (X.La C0 * X.a / (X.p * X.k)) := by ring
  have hL1 : X.La C0 * X.a / (X.p * X.k) ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := by
    rw [e1]; exact le_mul_of_one_le_left L0 hN1
  have e2 : X.La C0 / X.k * (4 * (X.a : ℝ) / X.p) = 4 * (X.La C0 * X.a / (X.p * X.k)) := by
    field_simp
  have e3 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) = (X.a : ℝ) / (X.p : ℝ) ^ 2 * (16 / X.p) := by
    field_simp
    ring
  have h16 : 16 / (X.p : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hp]; linarith
  have e4 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) ≤ 4 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) := by
    rw [e3, mul_comm 4]; exact mul_le_mul_of_nonneg_left h16 A1
  have e5 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 * X.b' / X.k) := by ring
  have e6 : 3 * X.b' / (X.p : ℝ) = 3 * (X.b' / X.p) := by ring
  have hO : localOrderCap C0 X ≤ 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) := by
    unfold localOrderCap
    rw [add_mul, e2, e5, e6]
    linarith
  have L1 : 0 ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := le_trans L0 hL1
  have hfirst : 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) ≤
      CE1 * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k) := by
    have hs : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k := by
      linarith
    have := mul_le_mul_of_nonneg_right h1 hs
    linarith
  have hkQ : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le hk hQ
  have hT : 0 ≤ X.k * X.N1 * X.Q * X.c := by positivity
  have t1 : X.k * X.N1 * X.Q * X.c ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = (X.k * X.Q) * (X.k * X.N1 * X.Q * X.c) := by ring
    rw [this]; exact le_mul_of_one_le_left hT hkQ
  have t2 : (X.N1 : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.N1 : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.N1 * (X.k * X.Q)) * X.c := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hcr
  have t3 : (X.c : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.c : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.c * (X.k * X.Q)) * X.N1 := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hN1
  have t4 : (X.c : ℝ) * ka1 X = 13 * (X.k * X.N1 * X.Q * X.c) := by unfold ka1; ring
  have hT2 : 0 ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := le_trans hT t1
  have hsecond : (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = CE2 * (X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c) := by ring
    rw [this, t4]
    have := mul_le_mul_of_nonneg_right h2 hT2
    linarith
  unfold Loc.E0 errorTermBound
  linarith

theorem room_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2)
    (n : ℕ) (hn1 : 1 ≤ n) (hnc : n ≤ X.c) (β : GlobalTheory X)
    (hβ : ∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) (a0 : Fin (numSeg X.TT) → ℕ)
    (ha0 : ∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p)
    (j0 j : Fin (numSeg X.TT)) :
    usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus := by
  classical
  set j' := rot _ j with hj'
  have hp0 : 0 < X.p := St.pP.pos
  have hqG : X.p ^ segG X.TT j' ≤ X.p ^ X.G' := Nat.pow_le_pow_right hp0 (St.segB j').1
  have hq1 : 1 ≤ X.p ^ segG X.TT j' := Nat.one_le_pow _ _ hp0

  have hN2 : (∑ i : Fin (segS X.TT j'), X.p ^ (segDists X.TT j').get i *
      ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)) ≤ X.N1 * ((X.m + 1) * X.p ^ X.G') := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin (segS X.TT j'))), X.p ^ (segDists X.TT j').get i *
        ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0) ≤ (X.m + 1) * X.p ^ X.G' := by
      intro i _
      have hd := (hβ j').1.1 i
      have s1 : (∑ c : Fin X.m, (β j').rz i c.succ) ≤ X.m * (X.seg C0 CE1 CE2 j').P X.p i := by
        have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin X.m)) (fun c => (β j').rz i c.succ)
          ((X.seg C0 CE1 CE2 j').P X.p i) (fun c _ => (hd c.succ).1.le)
        simpa using this
      have s2 : (β j').ry i 0 ≤ (X.seg C0 CE1 CE2 j').P X.p i := (hd 0).2.le
      calc X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)
          ≤ X.p ^ (segDists X.TT j').get i * ((X.m + 1) * (X.seg C0 CE1 CE2 j').P X.p i) :=
            Nat.mul_le_mul_left _ (by linarith)
        _ = (X.m + 1) * (X.p ^ (segDists X.TT j').get i * (X.seg C0 CE1 CE2 j').P X.p i) := by ring
        _ = (X.m + 1) * X.p ^ segG X.TT j' := by rw [pd_mul_P]
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ hqG
    have := Finset.sum_le_card_nsmul _ _ _ hi
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (St.segB j').2)

  have hN3 : X.c * (X.m * (X.p ^ segG X.TT j' - 1)) + (if j' = j0 then X.c else 0) ≤ X.c * ((X.m + 1) * X.p ^ X.G') := by
    obtain ⟨q', hq'⟩ : ∃ q', X.p ^ segG X.TT j' = q' + 1 := ⟨X.p ^ segG X.TT j' - 1, by omega⟩
    have hite : (if j' = j0 then X.c else 0) ≤ X.c := by split_ifs <;> omega
    have e : X.p ^ segG X.TT j' - 1 = q' := by omega
    rw [e]
    have h3 : X.m * q' + 1 ≤ (X.m + 1) * X.p ^ X.G' := by
      calc X.m * q' + 1 ≤ (X.m + 1) * (q' + 1) := by nlinarith
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ (hq' ▸ hqG)
    calc X.c * (X.m * q') + (if j' = j0 then X.c else 0) ≤ X.c * (X.m * q') + X.c := by omega
      _ = X.c * (X.m * q' + 1) := by ring
      _ ≤ X.c * ((X.m + 1) * X.p ^ X.G') := Nat.mul_le_mul_left _ h3
  have hnat : usedX X β a0 j0 j' ≤ (X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') := by
    unfold usedX
    linarith

  have hsum : ∑ i : Fin (segS X.TT j'), (if (i : ℕ) < (X.seg C0 CE1 CE2 j').sigma then ((β j').sg i : ℤ) else 0) =
      ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · rw [((hβ j').2.1 i (not_lt.1 h)).2.2.2]; rfl
  have hA := ha0 j'
  rw [hsum] at hA
  have hAr : ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) := by
    exact_mod_cast hA
  have hfl : ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j' : ℕ) : ℝ) := Int.floor_le _
  have hqr : (0 : ℝ) < ((X.p ^ segG X.TT j' : ℕ) : ℝ) := by exact_mod_cast hq1
  have hN1 : ((X.p ^ segG X.TT j' : ℕ) : ℝ) * ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤
      (X.a : ℝ) - X.E0 C0 CE1 CE2 := by
    have := (le_div_iff₀ hqr).1 (hAr.trans hfl)
    linarith

  have hc1 : 1 ≤ X.c := le_trans hn1 hnc
  have hka : 0 ≤ ka1 X := by
    unfold ka1
    have hk : (0 : ℝ) ≤ X.k := by have := St.N1k; have : (0 : ℝ) ≤ X.N1 := Nat.cast_nonneg _; linarith
    have hQ : (0 : ℝ) ≤ X.Q := by unfold Loc.Q; positivity
    positivity
  have hoP : ((β j).oPlus : ℝ) ≤ localOrderCap C0 X + (X.c : ℝ) * ka1 X := by
    have h := (hβ j).2.2.2.2
    have hcn : ((X.c - n : ℕ) : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have := mul_le_mul_of_nonneg_right hcn hka
    linarith
  have haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := (St.winA _ (next_mem X.TT j).1).1
  have hE := error_exponent_lower_bound St h1 h2 hc1
  have hreal : ((usedX X β a0 j0 j' + (β j).oPlus : ℕ) : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := by
    have hcast : ((usedX X β a0 j0 j' : ℕ) : ℝ) ≤
        (((X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') : ℕ) : ℝ) := by exact_mod_cast hnat
    have hk : X.k = (X.m : ℝ) + 1 := rfl
    have hQ : X.Q = (X.p : ℝ) ^ X.G' := rfl
    push_cast at hcast hN1 ⊢
    rw [hk, hQ] at hE
    linarith
  have : usedX X β a0 j0 j' + (β j).oPlus ≤ segAPlus X.TT X.aT j := by exact_mod_cast hreal
  omega

theorem threshold_standard_seventeen : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => (17 ≤ CE1 ∧ 17 ≤ CE2) ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ a1 a2 _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨⟨a1, a2⟩, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem restRoom : RestRoom :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc n hn1 hnc β hβ a0 ha0 j0 j =>
    room_of_std (h.2 X hD hH hc) h.1.1 h.1.2 n hn1 hnc β hβ a0 ha0 j0 j) threshold_standard_seventeen

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Exp

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def rPl (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0)) +
    (∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
    ∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)

def zPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))

def nPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

def stdE (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  rPl L j + Finsupp.single ((topEnd X j, true), 0) (segAPlus X.TT X.aT j - (β j).oPlus) + zPart C0 CE1 CE2 X β j +
    nPart C0 CE1 CE2 X β j

theorem stdPoly_eq (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (hsg : ∀ i : Fin (segS X.TT j), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0) :
    L.stdPoly O j = monomial (stdE L j) 1 := by
  classical
  have hd : digitMon (KK O) C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have hu : (∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l) =
      monomial (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) 1 := by
    rw [← uTop_sum (X.seg C0 CE1 CE2 j) (fun i => Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))), monomial_sum_one]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ
    rw [ioD_scal, ← pow_mul, X_pow_eq_monomial]
    rfl
  have hx : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) ^ (BDk C0 CE1 CE2 mu X β j).zPlus =
      monomial (Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (segAPlus X.TT X.aT j - (β j).oPlus)) 1 := by
    unfold scalZ
    rw [ioD_scalLast, X_pow_eq_monomial]
    rfl
  have hxi : (∏ c, ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m
      (BDk C0 CE1 CE2 mu X β j).T.t c)) ^ L.γ j c) =
      monomial (∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)) 1 := by
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [ioD_end β j 1 (by omega) _ (by rfl), X_pow_eq_monomial]
    rfl
  unfold LvDat.stdPoly
  simp only [map_mul, map_prod, map_pow]
  rw [hd, hs, hu, hx, hxi]
  simp only [monomial_mul, one_mul]
  congr 1
  unfold stdE rPl zPart nPart
  have hi : ∀ i : Fin (segS X.TT j),
      (∑ c : Fin (X.m + 1), (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) =
      Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0) +
      (∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
      Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i))) +
      Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0) +
      ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ) := by
    intro i
    rw [Fin.sum_univ_succ, Finset.sum_add_distrib, Finsupp.single_add]
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · simp only [if_pos h]
      abel
    · simp only [if_neg h, hsg i h, mul_zero, Finsupp.single_zero]
      abel
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (segS X.TT j)))) rfl (fun i _ => hi i)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_add_distrib] at hsum ⊢
  have key : ∀ (a b c d e x y u1 u2 u3 : MonH X), u1 + u2 + u3 = a + b + c + d + e →
      u1 + u2 + (u3 + x + y) = a + b + y + x + c + (d + e) := by
    intro a b c d e x y u1 u2 u3 h
    have : u1 + u2 + (u3 + x + y) = (u1 + u2 + u3) + (x + y) := by abel
    rw [this, h]
    abel
  rw [key _ _ _ _ _ _ _ _ _ _ hsum]

end Exp

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopOddNeEndAny
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Mk

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem mono_two (v1 v2 : VarH X) (a b : ℕ) :
    (monomial (Finsupp.single v1 a + Finsupp.single v2 b) (1 : KK O) : RHH O X) =
      MvPolynomial.X v1 ^ a * MvPolynomial.X v2 ^ b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

theorem softMk (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (C0 CE1 CE2 : ℝ) (a : IM X) :
    SoftOK S.w (fMk O C0 CE1 CE2 X a) (oMk C0 CE1 CE2 X a) (monomial (aMk C0 CE1 CE2 X a) 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · have h := softKSP S hS hD x.1 x.2 ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
    rw [sgKS_powP] at h
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)) 1) _
    rw [mono_two]
    exact h
  · have h := softKW S hS hD x.1 x.2.1 x.2.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softKS S hS hD x.1 x.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softLoc S.w hD h2 c
    show SoftOK S.w _ _ (monomial (∑ j : Fin (numSeg X.TT),
      Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)) 1) _
    rw [monomial_sum_one]
    have e : ∏ j : Fin (numSeg X.TT), (monomial (Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1)))
        (X.p ^ segG X.TT j - 1)) (1 : KK O) : RHH O X) = sgLoc O X := by
      unfold sgLoc
      exact Finset.prod_congr rfl fun j _ => by rw [X_pow_eq_monomial]
    rw [e]
    exact h

theorem fMk_pol (C0 CE1 CE2 : ℝ) (a : IM X) :
    fMk O C0 CE1 CE2 X a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · exact mem_Pol_iff.2 fun l => by
      have h := (mem_Pol_iff.1 (kS_pol (O := O) x.1 x.2) l).pow ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
      rw [smul_eq_mul] at h
      exact h
  · exact kW_pol x.1 x.2.1 _
  · exact kS_pol x.1 x.2
  · exact loc_pol _

end Mk

section Deg

variable {X : Loc}

theorem topStart_inj (X : Loc) : Function.Injective (topStart X) := by
  intro j j' h
  have h1 : (evenTops X.TT).get j = (evenTops X.TT).get j' := congrArg Subtype.val h
  have hnd : (evenTops X.TT).Nodup := Finset.sort_nodup _ _
  exact hnd.get_inj_iff.mp h1

theorem topOdd_ne_endAny (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (j' : Fin (numSeg X.TT)) :
    topOdd X j i ≠ topEnd X j' := by
  intro h
  have h1 : (segPos X.TT j i).val = (segNext X.TT j').val := congrArg (fun x : X.TT => (x.val : ℕ)) h
  exact (pos_mem X.TT j i).2 (h1 ▸ (next_mem X.TT j').2)

theorem pd_le (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i ≤ X.p ^ segG X.TT j :=
  Nat.pow_le_pow_right hD.1.pos (dist_pos_lt X.TT j i).2.le

theorem dgMk_le (hD : D1num X) (hG : ∀ j, segG X.TT j ≤ X.G') (C0 CE1 CE2 : ℝ) (a : IM X) (l : X.TT × Bool) :
    dgMk C0 CE1 CE2 X a l ≤ X.p ^ X.G' := by
  have hp : 1 ≤ X.p := hD.1.one_lt.le
  have hpG : ∀ j, X.p ^ segG X.TT j ≤ X.p ^ X.G' := fun j => Nat.pow_le_pow_right hp (hG j)
  have h1 : 1 ≤ X.p ^ X.G' := Nat.one_le_pow _ _ hp
  have hdl : ∀ j i, X.p ^ (segDists X.TT j).get i ≤ X.p ^ X.G' := fun j i => (pd_le hD j i).trans (hpG j)
  have hso : ∀ j i, topStart X j ≠ topOdd X j i := by
    intro j i h
    have h2 : (segStart X.TT j).val = (segPos X.TT j i).val := congrArg (fun x : X.TT => (x.val : ℕ)) h
    exact (pos_mem X.TT j i).2 (h2 ▸ (start_mem X.TT j).2)
  rcases a with x | x | x | x
  · obtain ⟨-, hdG⟩ := dist_pos_lt X.TT x.1 x.2
    have hPd : (X.seg C0 CE1 CE2 x.1).P X.p x.2 * X.p ^ (segDists X.TT x.1).get x.2 = X.p ^ segG X.TT x.1 := by
      show X.p ^ (segG X.TT x.1 - (segDists X.TT x.1).get x.2) * _ = _
      rw [← pow_add, Nat.sub_add_cancel hdG.le]
    have hPle : (X.seg C0 CE1 CE2 x.1).P X.p x.2 ≤ X.p ^ segG X.TT x.1 := by
      rw [← hPd]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · rw [mul_one, add_zero, hPd]
      exact hpG _
    · rw [mul_zero, zero_add, mul_one]
      exact hPle.trans (hpG _)
    · simp
  · simp only [dgMk, dgKW, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp [Ne.symm (hso x.1 x.2.1)])
    · simpa using h1
    · simpa using hdl x.1 x.2.1
    · simp
  · simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · simpa using hdl x.1 x.2
    · simpa using h1
    · simp
  · simp only [dgMk, dgLoc, dX]
    by_cases hex : ∃ j0, (topStart X j0, true) = l
    · obtain ⟨j0, hj0⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0, mul_one]
        exact (Nat.sub_le _ _).trans (hpG j0)
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        apply hj
        apply topStart_inj X
        rw [← hj0] at h
        exact (Prod.mk.inj h).1
      · intro h
        exact absurd (Finset.mem_univ j0) h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j _
        rw [if_neg (fun h => hex ⟨j, h⟩), mul_zero]

theorem dgMk_Y (C0 CE1 CE2 : ℝ) (a : IM X) (j' : Fin (numSeg X.TT)) : dgMk C0 CE1 CE2 X a (topEnd X j', false) = 0 := by
  rcases a with x | x | x | x <;>
    simp [dgMk, dgKS, dgKW, dgLoc, dX, topOdd_ne_endAny]

end Deg

section Sums

variable {X : Loc}

theorem bMk_eq (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    (∑ i : Fin (segS X.TT j), (β j).sg i • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j) +
        Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, (β j).rz i c.succ • ((Finsupp.single ((topOdd X j i, true), c.succ) 1 +
        Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), (β j).ry i 0 • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) +
        Finsupp.single ((topOdd X j i, false), 0) 1 : MonH X))) +
      Finsupp.single ((topStart X j, true), 0) (X.c * (X.m * (X.p ^ segG X.TT j - 1))))) = bMk C0 CE1 CE2 X β j := by
  unfold bMk
  simp only [Finsupp.single_add, smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  ext k
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_apply', Finsupp.single_apply]
  by_cases hs : ((topStart X j, true), (0 : Fin (X.m + 1))) = k
  · subst hs
    simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Fin.succ_ne_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf
  · simp only [hs, if_false, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf

theorem sum_aMk (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) :
    ∑ a, multMk X β a • aMk C0 CE1 CE2 X a = ∑ j, bMk C0 CE1 CE2 X β j := by
  simp only [← bMk_eq C0 CE1 CE2 β, Finset.sum_add_distrib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  · simp only [multMk, aMk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring

end Sums

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Rig

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def rig0 (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) : MonH X :=
  ∑ j, (rPl L j + Finsupp.single ((topEnd X j, true), 0) (segAPlus X.TT X.aT j - (β j).oPlus - usedX X β a0 j0 (rot _ j)))

def rig (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) : MonH X :=
  rig0 L a0 j0 + Finsupp.single ((topStart X j0, true), 0) X.c

theorem ndHom_single (v : VarH X) (n : ℕ) : ndHom X (Finsupp.single v n) = n * wN X v := by
  rw [← Finsupp.smul_single_one, map_nsmul, smul_eq_mul]
  congr 1
  show degUS (hhLetters X.TT) 1 (Finsupp.single v 1) = wN X v
  rw [Formalism.MainNotions.LemmaBAlt.degUS_single]
  rfl

theorem nd_rig (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) :
    ndM X (rig L a0 j0) = 0 := by
  show ndHom X (rig L a0 j0) = 0
  unfold rig rig0 rPl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, ndHom_single, normal_weight_vector_zero_eq_zero, wN_covS, mul_zero, Finset.sum_const_zero, add_zero]

theorem std_eq (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ)
    (j0 : Fin (numSeg X.TT))
    (hsg : ∀ j (i : Fin (segS X.TT j)), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0)
    (hroom : ∀ j, usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus)
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    Std = rig L a0 j0 + ((∑ j, (Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0 j) +
      zPart C0 CE1 CE2 X β j)) + ∑ j, bMk C0 CE1 CE2 X β j) := by
  classical
  have h1 : Std = ∑ j, stdE L j := by
    have : (monomial Std (1 : KK O) : RHH O X) = monomial (∑ j, stdE L j) 1 := by
      rw [hStd, monomial_sum_one]
      exact Finset.prod_congr rfl fun j _ => stdPoly_eq O L j (hsg j)
    exact monomial_left_injective (one_ne_zero) this
  rw [h1]
  set u1 : Fin (numSeg X.TT) → ℕ := fun j => X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1)) with hu1
  have hb : ∀ j, bMk C0 CE1 CE2 X β j = Finsupp.single ((topStart X j, true), 0) (u1 j) + nPart C0 CE1 CE2 X β j := by
    intro j
    unfold bMk nPart
    rw [add_assoc]
  have hus : ∀ j, usedX X β a0 j0 j = (X.seg C0 CE1 CE2 j).Qj X.p * a0 j + u1 j + (if j = j0 then X.c else 0) := by
    intro j
    unfold usedX
    show _ = X.p ^ segG X.TT j * a0 j + u1 j + _
    simp only [hu1]
    ring
  have hX : ∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j) =
      (∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).Qj X.p * a0 j)) +
      (∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (u1 j)) +
      Finsupp.single ((topStart X j0, true), (0 : Fin (X.m + 1))) X.c := by
    simp only [hus, Finsupp.single_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j0]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj, Finsupp.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hrot : ∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j) =
      ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 (rot _ j)) :=
    ((Equiv.ofBijective _ (rot_bij (numSeg X.TT))).sum_comp
      (fun j => Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j))).symm
  have hz : ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (segAPlus X.TT X.aT j - (β j).oPlus) =
      (∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1)))
        (segAPlus X.TT X.aT j - (β j).oPlus - usedX X β a0 j0 (rot _ j))) +
      ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 (rot _ j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finsupp.single_add, Nat.sub_add_cancel (hroom j)]
  unfold rig rig0 stdE
  simp only [hb, Finset.sum_add_distrib]
  rw [hz, ← hrot, hX]
  abel

end Rig

section Tot

variable {σ K : Type} [CommRing K] {J : Type} [Fintype J] {A : J → Type} [∀ j, Fintype (A j)] {B : J → Type}
  [∀ j, Fintype (B j)] {M : Type} [Fintype M]

theorem wh_total (ω : σ → ℕ) {sR : MvPolynomial σ K} {dR : ℕ} (hR : IsWeightedHomogeneous ω sR dR)
    {sC : ∀ j, A j → MvPolynomial σ K} {dC : ∀ j, A j → ℕ} (hC : ∀ j a, IsWeightedHomogeneous ω (sC j a) (dC j a))
    {sH : ∀ j, B j → MvPolynomial σ K} {dH : ∀ j, B j → ℕ} (hH : ∀ j i, IsWeightedHomogeneous ω (sH j i) (dH j i))
    {sM : M → MvPolynomial σ K} {dM : M → ℕ} (hM : ∀ a, IsWeightedHomogeneous ω (sM a) (dM a))
    (lv : ∀ j, B j → ℕ) (mult : M → ℕ) :
    IsWeightedHomogeneous ω (sR * ((∏ j, ∏ a, sC j a) * ((∏ j, ∏ i, sH j i ^ lv j i) * ∏ a, sM a ^ mult a)))
      (dR + ((∑ j, ∑ a, dC j a) + ((∑ j, ∑ i, lv j i * dH j i) + ∑ a, mult a * dM a))) := by
  have h1 := IsWeightedHomogeneous.prod Finset.univ (fun j => ∏ a, sC j a) (fun j => ∑ a, dC j a)
    (fun j _ => IsWeightedHomogeneous.prod Finset.univ (sC j) (dC j) fun a _ => hC j a)
  have h2 := IsWeightedHomogeneous.prod Finset.univ (fun j => ∏ i, sH j i ^ lv j i)
    (fun j => ∑ i, lv j i * dH j i)
    (fun j _ => IsWeightedHomogeneous.prod Finset.univ (fun i => sH j i ^ lv j i) (fun i => lv j i * dH j i)
      fun i _ => by simpa only [smul_eq_mul] using (hH j i).pow (lv j i))
  have h3 := IsWeightedHomogeneous.prod Finset.univ (fun a => sM a ^ mult a) (fun a => mult a * dM a)
    fun a _ => by simpa only [smul_eq_mul] using (hM a).pow (mult a)
  exact hR.mul (h1.mul (h2.mul h3))

end Tot

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Small

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

theorem top_letter_power_ne_zero (x : X.TT) (P : ℕ) (hP : P ≠ 0) : EhatT O X x P ≠ 0 := by
  intro h
  have key := congrArg (MvPolynomial.eval (fun v : (X.TT × Bool) × Fin (X.m + 1) => if v.2 = 0 then (1 : KK O) else 0)) h
  simp [EhatT, hP, Fin.succ_ne_zero] at key

theorem top_letter_ne_zero (x : X.TT) : hTop O X x ≠ 0 := by
  intro h
  have key := congrArg (MvPolynomial.eval (fun v : (X.TT × Bool) × Fin (X.m + 1) => if v.2 = 0 then (1 : KK O) else 0)) h
  simp [hTop, hKey, Fin.sum_univ_succ, Fin.succ_ne_zero] at key

theorem monomial_in_algebra (M : MonH X) : InA (monomial M (1 : KK O) : RHH O X) := by
  classical
  intro m
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem algebra_mul_mem {P Q : RHH O X} (hP : InA P) (hQ : InA Q) : InA (P * Q) := by
  rw [Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 (w := (1 : O))] at hP hQ ⊢
  exact Formalism.MainNotions.G.WittFrameLocaliserOrders.inWPow_zero_mul hP hQ

theorem algebra_prod_pow_mem {κ : Type} (s : Finset κ) (P : κ → RHH O X) (n : κ → ℕ) (h : ∀ a ∈ s, InA (P a)) :
    InA (∏ a ∈ s, P a ^ n a) := by
  rw [Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 (w := (1 : O))]
  refine Formalism.MainNotions.G.WittFrameLocaliserOrders.inWj_prod0 s _ (fun a ha => Formalism.MainNotions.G.WittFrameLocaliserOrders.inWPow_zero_pow ?_ _)
  exact (Formalism.MainNotions.G.WittFrameLocaliserOrders.inA_iff_inWj0 _).1 (h a ha)

theorem chain_embedding_injective (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

end Small

section Ord

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O] {w : O}
  {g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')}
  {J : Type} [Fintype J] {A : J → Type} [∀ j, Fintype (A j)] {B : J → Type} [∀ j, Fintype (B j)] {M : Type} [Fintype M]

theorem order_total_bound {sR : RHH O X} {dR : ℕ} (hR : InWjRg X.p X.n' O w 1 (hhLetters X.TT) g sR dR)
    {sC : ∀ j, A j → RHH O X} {dC : ∀ j, A j → ℕ} (hC : ∀ j a, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sC j a) (dC j a))
    {sH : ∀ j, B j → RHH O X} {dH : ∀ j, B j → ℕ} (hH : ∀ j i, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sH j i) (dH j i))
    {sM : M → RHH O X} {dM : M → ℕ} (hM : ∀ a, InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (sM a) (dM a))
    (lv : ∀ j, B j → ℕ) (mult : M → ℕ) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g
      (sR * ((∏ j, ∏ a, sC j a) * ((∏ j, ∏ i, sH j i ^ lv j i) * ∏ a, sM a ^ mult a)))
      (dR + ((∑ j, ∑ a, dC j a) + ((∑ j, ∑ i, lv j i * dH j i) + ∑ a, mult a * dM a))) := by
  refine inWjRg_mul hR (inWjRg_mul ?_ (inWjRg_mul ?_ ?_))
  · exact inWjRg_prod Finset.univ (fun j => ∏ a, sC j a) (fun j => ∑ a, dC j a)
      (fun j _ => inWjRg_prod Finset.univ (sC j) (dC j) (fun a _ => hC j a))
  · exact inWjRg_prod Finset.univ (fun j => ∏ i, sH j i ^ lv j i) (fun j => ∑ i, lv j i * dH j i)
      (fun j _ => inWjRg_prod Finset.univ (fun i => sH j i ^ lv j i) (fun i => lv j i * dH j i)
        (fun i _ => inWjRg_pow (hH j i) (lv j i)))
  · exact inWjRg_prod Finset.univ (fun a => sM a ^ mult a) (fun a => mult a * dM a)
      (fun a _ => inWjRg_pow (hM a) (mult a))

end Ord

def multMk0 (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inr (Sum.inr (Sum.inr _)) => 0
  | a => multMk X β a

theorem product_split_constant {O : Type} [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) :
    ∏ a, fMk O C0 CE1 CE2 X a ^ multMk X β a =
      (∏ a, fMk O C0 CE1 CE2 X a ^ multMk0 X β a) * ∏ c : Fin X.m, locC O X c.succ ^ X.c := by
  simp only [Fintype.prod_sum_type, multMk0, multMk, fMk, pow_zero, Finset.prod_const_one, mul_one]
  simp only [mul_assoc]

theorem sum_split_constant (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) :
    ∑ a, multMk0 X β a * oMk C0 CE1 CE2 X a = ∑ a, multMk X β a * oMk C0 CE1 CE2 X a := by
  simp [Fintype.sum_sum_type, multMk0, multMk, oMk]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

def l2P (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : ℕ :=
  (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) i)

def l2x (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : X.TT :=
  topOdd X j (uTop (X.seg C0 CE1 CE2 j) i)

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] {β : GlobalTheory X}

def l2sR (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ)
    (j0 : Fin (numSeg X.TT)) : RHH O X :=
  (∏ j, hTop O X (topEnd X j) ^ L.jp j) * monomial (rig L a0 j0) 1

theorem lifted_block_generator (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i) =
      EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) := ioD_Ehat β j i

theorem rigid_factor_product (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) :
    (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) *
      monomial (rig L a0 j0) 1 = l2sR O L a0 j0 := by
  unfold l2sR
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [ioD_Eplus]

theorem rigid_product_weighted_homog (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT))
    (ω : VarH X → ℕ) (e : X.TT → ℕ) (he : ∀ x, IsWeightedHomogeneous ω (hTop O X x) (e x)) :
    IsWeightedHomogeneous ω (l2sR O L a0 j0) ((∑ j, L.jp j * e (topEnd X j)) + Finsupp.weight ω (rig L a0 j0)) := by
  unfold l2sR
  refine IsWeightedHomogeneous.mul ?_ (isWeightedHomogeneous_monomial _ _ _ rfl)
  have h := IsWeightedHomogeneous.prod Finset.univ (fun j => hTop O X (topEnd X j) ^ L.jp j)
    (fun j => L.jp j • e (topEnd X j)) (fun j _ => (he _).pow _)
  simpa [smul_eq_mul] using h

theorem word_head_formula (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    L.head O j (L.lv j) G = (∏ i, EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
      hTop O X (topEnd X j) ^ L.jp j * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) G) := by
  unfold LvDat.head
  rw [map_mul, map_mul, map_prod, map_pow, ioD_Eplus]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [map_pow, lifted_block_generator]

theorem sym_family_word_eq_head_mul_monomial (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
  unfold symFam
  rw [hStd, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => L.ioBlock_word O j (G j)

theorem sym_family_word_ne_zero (hp : 0 < X.p) (L : LvDat C0 CE1 CE2 mu X β)
    (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (hG0 : ∀ j, G j ≠ 0)
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) ≠ 0 := by
  rw [sym_family_word_eq_head_mul_monomial L G Std hStd]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => ?_) ?_
  · rw [word_head_formula]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
      (top_letter_power_ne_zero _ _ (pow_pos hp _).ne')) (pow_ne_zero _ (top_letter_ne_zero _))) (ioD_ne_zero hp β j ?_)
    intro h
    exact hG0 j (rename_injective _ (chain_embedding_injective _ _ _) (by rw [h, map_zero]))
  · intro h
    exact one_ne_zero (monomial_eq_zero.1 h)

theorem balanced_word_homogeneous (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
    (hGpol : ∀ j, G j ∈ Pol (KK O) X.m (L.LL j).deg) :
    BalHom O C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  intro j ω' ωL hb
  refine gen_wh O X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j) ω' ωL hb.1 hb.2.1 hb.2.2
    (L.lv j) (L.jp j) (L.ok j) (G j) (hGpol j) _ ?_
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun c => (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) :
      MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O)) ^ L.γ j c) _
    (fun c _ => (isWeightedHomogeneous_X (KK O) ω' _).pow (L.γ j c))
  refine wh_congr h ?_
  rw [← L.hγ j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact hb.1 _ _

end Ctx

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {β : GlobalTheory X} {L : LvDat C0 CE1 CE2 mu X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)}

def l2sC (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) (a : (Cs j).ι) : RHH O X :=
  monomial ((Cs j).pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) ((Cs j).Kc a))

theorem column_word_mem_polynomials_of_degree (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) :
    G j ∈ Pol (KK O) X.m (L.LL j).deg := by
  have h := Formalism.L2.G.Model.Pol_prod (R := KK O) (k := X.m) Finset.univ (Cs j).dK (Cs j).Kc
    (fun a _ => (Cs j).KPol a)
  rw [(Cs j).Kprod] at h
  have hd : ∑ a, (Cs j).dK a = (L.LL j).deg := funext fun i => by rw [Finset.sum_apply, (Cs j).dKsum i]
  rwa [hd] at h

theorem column_product_eq_monomial_mul_ioD (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) :
    ∏ a, l2sC Cs j a = monomial (∑ a, (Cs j).pl a) 1 *
      ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (G j)) := by
  unfold l2sC
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, (Cs j).Kprod, MvPolynomial.monomial_sum_one]

theorem sym_family_eq_sigma_product (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j0 : Fin (numSeg X.TT)) (Std : MonH X)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (stdEq : Std = rig L (fun j => (Cs j).a0) j0 +
      ((∑ j, ∑ a, (Cs j).pl a) + ∑ a, multMk X β a • aMk C0 CE1 CE2 X a)) :
    l2sR O L (fun j => (Cs j).a0) j0 * ((∏ j, ∏ a, l2sC Cs j a) *
      ((∏ j, ∏ i, EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
      ∏ a, (monomial (aMk C0 CE1 CE2 X a) (1 : KK O) : RHH O X) ^ multMk X β a)) =
      symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hMprod : ∏ a, (monomial (aMk C0 CE1 CE2 X a) (1 : KK O) : RHH O X) ^ multMk X β a =
      monomial (∑ a, multMk X β a • aMk C0 CE1 CE2 X a) 1 := (mono_sum _ _ _).symm
  have hmono : (monomial Std (1 : KK O) : RHH O X) = monomial (rig L (fun j => (Cs j).a0) j0) 1 *
      ((∏ j, monomial (∑ a, (Cs j).pl a) 1) * monomial (∑ a, multMk X β a • aMk C0 CE1 CE2 X a) 1) := by
    rw [← monomial_sum_one, monomial_mul, monomial_mul, one_mul, one_mul, ← stdEq]
  rw [sym_family_word_eq_head_mul_monomial L G Std hStd, hmono, hMprod]
  simp only [word_head_formula, column_product_eq_monomial_mul_ioD, Finset.prod_mul_distrib]
  unfold l2sR
  ring

end Ctx

end Formalism.MainNotions.ColumnSystems.Pf
