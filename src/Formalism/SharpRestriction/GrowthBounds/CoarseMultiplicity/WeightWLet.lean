module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockWh
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def TD (b : SegBlock (segS X.TT j) X.m) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j),
    ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0)))) +
  (segAPlus X.TT X.aT j - b.oPlus) * ω ((topEnd X j, true), 0) + b.oPlus * ω ((topEnd X j, true), Fin.succ 0) +
    (X.seg C0 CE1 CE2 j).bPlus * ω ((topEnd X j, false), Fin.succ 0)

theorem ioBlock_wh (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : s ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b).SSZ O (r := X.m)) :
    IsWeightedHomogeneous ω (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (TD C0 CE1 CE2 X j b ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ := fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) + ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU l
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hS := ssz_wh O X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b ω' ωL h1 h2 h3 s hs
  have hA := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) s _ hS
  have hDg : IsWeightedHomogeneous ω (digitMon (KK O) C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (b.rz i c • ω ((topOdd X j i, true), c) + b.ry i c • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have hSt : IsWeightedHomogeneous ω (sTopMon (KK O) X.p C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) • ω ((topOdd X j i, true), 0) +
          ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i) • ω ((topOdd X j i, false), 0) else 0) := by
    refine IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?_)
    split_ifs
    · exact ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)
    · exact isWeightedHomogeneous_one _ _
  have hall := (hDg.mul hSt).mul hA
  refine wh_congr hall ?_
  have E1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ω' (Sum.inr (Fin.castSucc l, false)) =
      ∑ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0 := by
    rw [← sum_uTop (X.seg C0 CE1 CE2 j) (fun i => (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ]
    rfl
  have E3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      b.oPlus * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU, chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl, chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl]
  unfold OmB TD
  rw [E1, E3, hx, hXi]
  simp only [smul_eq_mul, Bool.not_false]
  have key : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0))) =
      (∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          (X.seg C0 CE1 CE2 j).P X.p i * b.sg i * ω ((topOdd X j i, false), 0) else 0) +
      (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0) +
      ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    intro i
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, if_neg (not_le.2 h), if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_pos (not_lt.1 h), if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LogLeOfLeSq
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem natPart {n' : ℕ} (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (f : Fin n' → ℕ) :
    ∏ s ∈ TT, f s = ∏ j, (f (segNext TT j) * ∏ i, f (segPos TT j i)) := by
  have h := prod_tops TT h2 (fun s => (f s : ℝ))
  rw [Finset.prod_mul_distrib, ← prod_next TT (fun s => (f s : ℝ)), ← Finset.prod_mul_distrib] at h
  exact_mod_cast h

theorem natPartSum {n' : ℕ} (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (g : Fin n' → ℕ) :
    ∑ s ∈ TT, g s = ∑ j, (g (segNext TT j) + ∑ i, g (segPos TT j i)) := by
  have h := natPart TT h2 (fun s => 2 ^ g s)
  simp only [Finset.prod_pow_eq_pow_sum, ← pow_add] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem ft_prod_letters {n' : ℕ} {M : Type} [CommMonoid M] (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (F : ℕ → M) :
    ∏ x : TT × Bool, F (hhDegs TT aT bT x) = ∏ s ∈ TT, (F (aT s) * F (bT s)) := by
  rw [Fintype.prod_prod_type, ← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fintype.prod_bool]
  unfold hhDegs hhDeg
  by_cases he : Even s.val.val
  · simp [he]
  · simp [he, mul_comm]

theorem facSeg_prod (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    ∏ x : X.TT × Bool, (hhDegs X.TT X.aT X.bT x).factorial = ∏ j, facSeg X j := by
  rw [ft_prod_letters X.TT X.aT X.bT Nat.factorial, natPart X.TT h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold facSeg
  rw [Finset.prod_congr rfl fun i _ => mul_comm ((X.bT (segPos X.TT j i)).factorial) _]
  ring

theorem lgSeg_sum (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    ∑ j, lgSeg X j = ∑ s ∈ X.TT, (Nat.log X.p (X.aT s) + Nat.log X.p (X.bT s)) := by
  rw [natPartSum X.TT h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold lgSeg
  rw [Finset.sum_congr rfl fun i _ => add_comm (Nat.log X.p (X.bT (segPos X.TT j i))) _]
  ring

theorem kapZ_sum (X : Loc) (h2 : 2 ≤ numSeg X.TT) :
    kapZ X.p X.m X.TT X.aT X.bT = ∑ j, (X.m + 1) * lgSeg X j := by
  rw [← Finset.mul_sum, lgSeg_sum X h2]
  unfold kapZ
  rw [← Finset.mul_sum]
  congr 1
  have := ft_prod_letters (M := Multiplicative ℕ) X.TT X.aT X.bT (fun d => Multiplicative.ofAdd (Nat.log X.p d))
  exact this

theorem zProdAt : ZProdAt := by
  intro X K _ h2
  unfold zTen zSeg
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← kapZ_sum X h2]
  congr 1
  have := congrArg (Nat.cast (R := K)) (facSeg_prod X h2)
  push_cast at this
  exact this

theorem log_le_of_le_sq {p a d : ℕ} (hp : 1 < p) (ha : 1 ≤ a) (hd : d ≤ a ^ 2) :
    (Nat.log p d : ℝ) ≤ 2 * Real.logb p a := by
  have hp' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hnn : 0 ≤ Real.logb p a := Real.logb_nonneg hp' ha'
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    positivity
  · have h1 : (Nat.log p d : ℝ) ≤ Real.logb p d := Real.natLog_le_logb d p
    have h2 : Real.logb p d ≤ Real.logb p ((a : ℝ) ^ 2) :=
      Real.logb_le_logb_of_le hp' (by exact_mod_cast h0) (by exact_mod_cast hd)
    rw [Real.logb_pow] at h2
    push_cast at h2
    linarith

theorem numAt (C0 Cde CE1 CE2 : ℝ) : NumAt C0 Cde CE1 CE2 := by
  intro X St
  have hp1 : 1 < X.p := by have := St.p5; omega
  have hk : (1 : ℝ) ≤ X.k := by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith

  have ha0 : 0 < (X.a : ℝ) := by
    rcases Nat.eq_zero_or_pos X.a with h | h
    · have := St.loga
      rw [h] at this
      simp at this
      linarith
    · exact_mod_cast h
  have hae : Real.exp 1 ≤ (X.a : ℝ) := (Real.le_log_iff_exp_le ha0).1 St.loga
  have ha3 : 3 ≤ X.a := by
    by_contra hlt
    have : X.a ≤ 2 := by omega
    have h2 : (X.a : ℝ) ≤ 2 := by exact_mod_cast this
    have := Real.exp_one_gt_d9
    linarith
  have ha3' : (3 : ℝ) ≤ (X.a : ℝ) := by exact_mod_cast ha3
  have hA : ∀ s ∈ X.TT, X.aT s ≤ X.a ^ 2 := by
    intro s hs
    have h1 := (St.winA s hs).2
    have hkY : 1 ≤ X.k * X.Y := by nlinarith [St.Y1]
    have h2 : 2 / (X.k * X.Y) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h3 : (X.aT s : ℝ) ≤ (X.a : ℝ) ^ 2 := by nlinarith
    exact_mod_cast h3
  have hB : ∀ s ∈ X.TT, X.bT s ≤ X.a ^ 2 := by
    intro s hs
    have h1 := (St.winB s hs).2
    have hN1 : (0 : ℝ) ≤ 18 * X.N1 * X.La C0 / X.k := by
      have : (0 : ℝ) ≤ (X.N1 : ℝ) := Nat.cast_nonneg _
      have h' := St.La1
      positivity
    have hbe : be X C0 ≤ 1 := by
      have := St.beLe
      have := St.de6
      linarith
    have hb : X.b' * (X.p : ℝ) < X.a := by
      have := St.pab
      rw [lt_div_iff₀ St.bpos] at this
      linarith
    have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by exact_mod_cast St.p5
    have hb2 : 2 * X.b' ≤ X.a := by nlinarith [St.bpos]
    have h3 : (X.bT s : ℝ) ≤ (X.a : ℝ) ^ 2 := by nlinarith [St.bpos]
    exact_mod_cast h3
  have hnn : 0 ≤ Real.logb X.p X.a :=
    Real.logb_nonneg (by exact_mod_cast hp1) (by linarith)
  have hsum : ((∑ j, lgSeg X j : ℕ) : ℝ) ≤ X.N * (4 * Real.logb X.p X.a) := by
    rw [lgSeg_sum X St.seg2]
    push_cast
    unfold Loc.N
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    have h1 := log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hA s hs)
    have h2 := log_le_of_le_sq hp1 (by omega : 1 ≤ X.a) (hB s hs)
    linarith
  have e1 : ∑ j : Fin (numSeg X.TT), (((X.m + 2) * lgSeg X j : ℕ) : ℝ) = ((X.m : ℝ) + 2) * ((∑ j, lgSeg X j : ℕ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
  rw [e1]
  unfold Loc.kap0 kap0G4
  have hN : 0 ≤ X.N := by unfold Loc.N; positivity
  have hm : (X.m : ℝ) + 2 ≤ 2 * X.k := by unfold Loc.k; have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith
  have hm0 : (0 : ℝ) ≤ (X.m : ℝ) + 2 := by positivity
  calc ((X.m : ℝ) + 2) * ((∑ j, lgSeg X j : ℕ) : ℝ) ≤ ((X.m : ℝ) + 2) * (X.N * (4 * Real.logb X.p X.a)) :=
        mul_le_mul_of_nonneg_left hsum hm0
    _ ≤ (2 * X.k) * (X.N * (4 * Real.logb X.p X.a)) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = 4 * (2 * X.N * X.k * Real.logb X.p X.a) := by ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def OPlusAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → ∀ (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m), Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    b.oPlus ≤ segAPlus X.TT X.aT j

def wLet (X : Loc) (x : X.TT × Bool) : (X.TT × Bool) × Fin (X.m + 1) → ℕ := fun v => if v.1 = x then 1 else 0

theorem weight_wLet (X : Loc) (x : X.TT × Bool) (μ : (X.TT × Bool) × Fin (X.m + 1) →₀ ℕ) :
    Finsupp.weight (wLet X x) μ = multideg μ x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype μ (fun v k => k • wLet X x v) (fun _ => zero_smul _ _),
    Fintype.sum_prod_type, Finset.sum_eq_single x]
  · unfold multideg wLet
    simp
  · intro y _ hy
    unfold wLet
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem TD_wLet (x : X.TT × Bool) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    TD C0 CE1 CE2 X j b (wLet X x) =
      (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  obtain ⟨t, bb⟩ := x
  have hterm : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * wLet X (t, bb) ((topOdd X j i, true), c) +
          b.ry i c * wLet X (t, bb) ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.sg i * wLet X (t, bb) ((topOdd X j i, false), 0) + b.w i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.o i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0))) =
      (if segPos X.TT j i = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    intro i
    have hodd := (pos_mem X.TT j i).2
    by_cases h : segPos X.TT j i = t.val
    · have ht : topOdd X j i = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.2 i
        have hPC : (X.seg C0 CE1 CE2 j).P X.p i * coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
            segATop X.TT X.aT j i - ∑ c, b.ry i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            b.sg i + (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i)
            else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) =
            coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.2.1
            omega
          · rfl
        rw [hin, hPC, hdeg]
        have := hd.1
        omega
      · have w1 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.1 i
        have hPA : (X.seg C0 CE1 CE2 j).P X.p i * coarseA X.p (X.seg C0 CE1 CE2 j) b i =
            (X.seg C0 CE1 CE2 j).bTop i - ∑ c, b.rz i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i + b.w i
            else coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i + b.o i) = coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.1
            omega
          · have := (hk.2.1 i (not_lt.1 hs)).1
            omega
        rw [hin, hPA, hdeg]
        have := hd.1
        omega
    · have w0 : ∀ b' c, wLet X (t, bb) ((topOdd X j i, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero, Finset.sum_const_zero, ite_self]
  have hend : (segAPlus X.TT X.aT j - b.oPlus) * wLet X (t, bb) ((topEnd X j, true), 0) +
      b.oPlus * wLet X (t, bb) ((topEnd X j, true), Fin.succ 0) +
      (X.seg C0 CE1 CE2 j).bPlus * wLet X (t, bb) ((topEnd X j, false), Fin.succ 0) =
      (if segNext X.TT j = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    have hev := (next_mem X.TT j).2
    by_cases h : segNext X.TT j = t.val
    · have ht : topEnd X j = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add]
        show X.bT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) false
        unfold hhDeg
        simp [hev]
      · have w1 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, add_zero]
        rw [Nat.sub_add_cancel ho]
        show X.aT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) true
        unfold hhDeg
        simp [hev]
    · have w0 : ∀ b' c, wLet X (t, bb) ((topEnd X j, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero]
  unfold TD
  rw [Finset.sum_congr rfl fun i _ => hterm i, add_assoc, add_assoc, ← add_assoc ((segAPlus X.TT X.aT j - b.oPlus) * _),
    hend, add_comm]

end Formalism.MainNotions.ColumnSystems.Pf
