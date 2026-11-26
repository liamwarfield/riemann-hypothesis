module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreDef
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.GenWh
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDScalLast
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoBlockNeZero
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section TDs

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem TD_wLetBL {Cde E : ℝ} (x : X.TT × Bool) (b : SegBlock (segS X.TT j) X.m)
    (hk : BLk C0 Cde CE1 CE2 X E j b) :
    TD C0 CE1 CE2 X j b (wLet X x) =
      (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have ho : b.oPlus ≤ segAPlus X.TT X.aT j := hk.2.2.2.1
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

theorem TD_wN (b : SegBlock (segS X.TT j) X.m) :
    TD C0 CE1 CE2 X j b (wN X) = blockOrd X.p (X.seg C0 CE1 CE2 j) b := by
  unfold TD blockOrd oEff
  simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ c : Fin (X.m + 1), (b.rz i c * wN X ((topOdd X j i, true), c) + b.ry i c * wN X ((topOdd X j i, false), c)) =
      (∑ c : Fin (X.m + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero, Fin.val_zero, if_true,
      Fin.val_succ, Nat.succ_ne_zero, if_false]
    ring
  rw [h1]
  split_ifs <;> ring

end TDs

section Sym

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O]

def BalHom (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' (s j)
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (β j) ω' ωL)

theorem symPolBL (h2 : 2 ≤ numSeg X.TT) {E : ℝ} (β : GlobalTheory X) (hβ : ∀ j, BLk C0 Cde CE1 CE2 X E j (β j))
    (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    symFam (KK O) X.p C0 CE1 CE2 X β s ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) := by
  classical
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro μ hμ x
  have hwh : IsWeightedHomogeneous (wLet X x) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wLet X x)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wLet X x) (fun _ _ _ => rfl)
      (fun _ => rfl) rfl (s j) (hs j))
  have h1 := hwh (mem_support_iff.1 (Finset.mem_coe.1 hμ))
  rw [weight_wLet] at h1
  rw [h1, Finset.sum_congr rfl fun j _ => TD_wLetBL C0 CE1 CE2 X j x (β j) (hβ j),
    ← natPartSum X.TT h2 (fun s => if s = x.1.val then hhDegs X.TT X.aT X.bT x else 0), Finset.sum_ite_eq',
    if_pos x.1.2]

theorem symNdBL (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s) (ordFam C0 CE1 CE2 X β) := by
  have hwh : IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wN X)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wN X)
      (fun x c c' => by
        rcases x with ⟨t, bb⟩
        cases bb
        · rw [wN_covS, wN_covS]
        · rw [wN_vecS, wN_vecS])
      (fun l => by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS])
      (by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS]) (s j) (hs j))
  have e : ∑ j, TD C0 CE1 CE2 X j (β j) (wN X) = ordFam C0 CE1 CE2 X β :=
    Finset.sum_congr rfl fun j _ => TD_wN C0 CE1 CE2 X j (β j)
  rwa [e] at hwh

theorem ioBlock_coeff (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    (ioBlock (KK O) X.p C0 CE1 CE2 X j b u).coeff (ioExp C0 CE1 CE2 X j b μ) = u.coeff μ := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial ν c =>
    rw [ioBlock_monomial, coeff_monomial, coeff_monomial]
    by_cases h : ν = μ
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg fun e => h (ioExp_inj C0 CE1 CE2 X hp j b e)]
  | add p q hp' hq' => rw [ioBlock_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp', hq']

theorem ioBlock_ne_zero (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    {u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)} (hu : u ≠ 0) : ioBlock (KK O) X.p C0 CE1 CE2 X j b u ≠ 0 := by
  intro h
  apply hu
  ext μ
  rw [← ioBlock_coeff hp j b u μ, h]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem ioD_ne_zero (hp : 0 < X.p) {mu : ℝ} (β : GlobalTheory X) (j : Fin (numSeg X.TT))
    {u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O)} (hu : u ≠ 0) :
    ioD O C0 CE1 CE2 mu X β j u ≠ 0 := by
  intro h
  refine ioBlock_ne_zero (C0 := C0) (CE1 := CE1) (CE2 := CE2) hp j (β j) (u := u) hu ?_
  show digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) * ioD O C0 CE1 CE2 mu X β j u = 0
  rw [h, mul_zero]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Io

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] (β : GlobalTheory X) (j : Fin (numSeg X.TT))

theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem ioD_scal (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.castSucc l, bb))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !bb), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  rw [ioD_X]
  have hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t := l.2
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  rfl

theorem ioD_scalLast (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t, bb))) =
      MvPolynomial.X ((topEnd X j, !bb), 0) := by
  rw [ioD_X]
  have hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) <
      (X.seg C0 CE1 CE2 j).t := lt_irrefl _
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]

theorem ioD_odd (i : Fin (segS X.TT j)) (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * i + e)
    (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topOdd X j i, decide (e = 0)), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i := by
  rw [ioD_X]
  have hi := i.2
  have hl : (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  have e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by simp only; omega)
  have e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e1, e2]

theorem ioD_end (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * segS X.TT j + e) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topEnd X j, decide (e = 0)), c.succ) := by
  rw [ioD_X]
  have hl : ¬ (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]
  have e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e2]

theorem ioD_Ehat (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l) =
      EhatT O X (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l)) ((X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l)) := by
  unfold BlockData.Ehat EhatT scalZ scalS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_mul, map_sum, ioD_scal, ioD_scal]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hu := (uTop (X.seg C0 CE1 CE2 j) l).2
  rw [map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _
      omega),
    ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ) + 1) (2 * segS X.TT j + 1) = _
      omega)]
  rfl

theorem ioD_Eplus :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) = hTop O X (topEnd X j) := by
  unfold hTop hKey
  rw [Fin.sum_univ_succ]
  unfold BlockData.Eplus scalZ scalS xiVar
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_mul, map_sum, ioD_scalLast, ioD_scalLast]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]
  rfl

end Io

theorem uTop_sum {s : ℕ} {M : Type} [AddCommMonoid M] (S : SegData s) (F : Fin s → M) :
    ∑ l : Fin S.t, F (uTop S l) = ∑ i : Fin s, if (i : ℕ) < S.sigma then 0 else F i := by
  classical
  have h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < S.sigma <;> simp [h]
  rw [h1]
  refine Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]
    omega
  · intro l _ l' _ h
    have := congrArg Fin.val h
    simp only [uTop] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := i.2
      unfold SegData.t
      omega
    · apply Fin.ext
      simp only [uTop]
      omega
  · intro l _
    rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Gen

variable {s r : ℕ}

private theorem gen_wh_of_pos_separated_of_le_deg {N T : ℕ} (deg : Fin N → ℕ) (pos : Fin T → ℕ) (j : Fin T → ℕ) (u : Fin N) (jp : ℕ)
    (w : Fin N → ℕ) (hpos : ∀ i, pos i + 1 < N) (hu : ∀ i, pos i + 1 < (u : ℕ))
    (hdis : ∀ i i', i ≠ i' → pos i ≠ pos i' ∧ pos i ≠ pos i' + 1 ∧ pos i + 1 ≠ pos i')
    (hj : ∀ i, j i ≤ deg ⟨pos i, by have := hpos i; omega⟩ ∧ j i ≤ deg ⟨pos i + 1, hpos i⟩)
    (hjp : jp ≤ deg u) :
    ∑ a, ((deg a - ∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) - if a = u then jp else 0) * w a
      + (∑ i, j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) + jp * w u)
      = ∑ a, deg a * w a := by
  have key : ∀ a : Fin N, (∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0)
      + (if a = u then jp else 0) ≤ deg a := by
    intro a
    by_cases hau : a = u
    · subst hau
      have hn : ∀ i, ¬ ((a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1) := fun i h => by
        have := hu i
        omega
      simp only [hn, if_false, Finset.sum_const_zero, if_true, zero_add]
      exact hjp
    · rw [if_neg hau, add_zero]
      by_cases hex : ∃ i0, (a : ℕ) = pos i0 ∨ (a : ℕ) = pos i0 + 1
      · obtain ⟨i0, h0⟩ := hex
        rw [Finset.sum_eq_single i0]
        · rw [if_pos h0]
          rcases h0 with h0 | h0
          · have h' := (hj i0).1
            have ha : a = ⟨pos i0, by have := hpos i0; omega⟩ := Fin.ext h0
            rw [ha]
            exact h'
          · have h' := (hj i0).2
            have ha : a = ⟨pos i0 + 1, hpos i0⟩ := Fin.ext h0
            rw [ha]
            exact h'
        · intro i _ hi
          rw [if_neg]
          intro h
          have := hdis i i0 hi
          omega
        · intro h
          exact absurd (Finset.mem_univ i0) h
      · push_neg at hex
        rw [Finset.sum_eq_zero]
        · exact Nat.zero_le _
        · intro i _
          rw [if_neg]
          rintro (h | h)
          · exact (hex i).1 h
          · exact (hex i).2 h
  have split : ∀ i, ∑ a : Fin N, (if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) * w a
      = j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) := by
    intro i
    have hs : ∀ a : Fin N, (if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0)
        = (if a = ⟨pos i, by have := hpos i; omega⟩ then j i else 0)
          + (if a = ⟨pos i + 1, hpos i⟩ then j i else 0) := by
      intro a
      by_cases h1 : (a : ℕ) = pos i
      · have h2 : a ≠ ⟨pos i + 1, hpos i⟩ := fun h => by
          rw [h] at h1
          simp at h1
        rw [if_pos (Or.inl h1), if_pos (Fin.ext h1), if_neg h2, add_zero]
      · by_cases h3 : (a : ℕ) = pos i + 1
        · have h2 : a ≠ ⟨pos i, by have := hpos i; omega⟩ := fun h => h1 (by rw [h])
          rw [if_pos (Or.inr h3), if_neg h2, if_pos (Fin.ext h3), zero_add]
        · have h2 : a ≠ ⟨pos i, by have := hpos i; omega⟩ := fun h => h1 (by rw [h])
          have h4 : a ≠ ⟨pos i + 1, hpos i⟩ := fun h => h3 (by rw [h])
          rw [if_neg (by tauto), if_neg h2, if_neg h4, add_zero]
    simp only [hs, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_add]
  have hB : ∑ a : Fin N, (if a = u then jp else 0) * w a = jp * w u := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hA : ∑ a : Fin N, (∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) * w a
      = ∑ i, j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => split i)
  rw [← hA, ← hB, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← add_mul, ← add_mul, Nat.sub_sub, Nat.sub_add_cancel (key a)]

theorem gen_wh (O : Type) [CommRing O] [IsDomain O] [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (mm : ℝ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a)
    (h2 : ∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))
    (h3 : ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _))
    (jl : Fin (blockData p S aTop aPlus mm b).T.t → ℕ) (jp : ℕ) (hlev : (blockData p S aTop aPlus mm b).LevelOK jl jp)
    (y : MvPolynomial (Fin (2 * s + 1) × Fin r) (KK O))
    (hy : y ∈ Pol (KK O) r ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg)
    (g : MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t) (KK O))
    (hG : IsWeightedHomogeneous ω g (((blockData p S aTop aPlus mm b).B - jp) * ωL (Fin.last _))) :
    IsWeightedHomogeneous ω
      ((∏ i, (blockData p S aTop aPlus mm b).Ehat O (r := r) i ^ jl i) * (blockData p S aTop aPlus mm b).Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.castSucc i)) ^ (blockData p S aTop aPlus mm b).T.z i) *
      X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.last (blockData p S aTop aPlus mm b).T.t)) ^
        (blockData p S aTop aPlus mm b).zPlus *
      rename (chainEmb (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t) y * g) (OmB p S aTop aPlus b ω ωL) := by
  have hE : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Ehat O (r := r) i)
        (ωL (finPos (2 * s + 1) (2 * (uTop S i : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S i : ℕ) + 1))) := by
    intro i
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ (fun c _ => ?_))
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact h2 i
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact congrArg₂ (· + ·) (h1 _ c) (h1 _ c)
  have hP : IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Eplus O (r := r))
      (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) := by
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ (fun c _ => ?_))
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact h3
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact congrArg₂ (· + ·) (h1 _ c) (h1 _ c)
  have hEp := IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => (hE i).pow (jl i))
  have hZp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.castSucc i)) ^ (blockData p S aTop aPlus mm b).T.z i)
    _ (fun i _ => (isWeightedHomogeneous_X (KK O) ω _).pow _)
  have hC := wh_chain ω ωL h1 _ y hy
  refine wh_congr ((((((hEp.mul (hP.pow jp)).mul hZp).mul ((isWeightedHomogeneous_X (KK O) ω _).pow _)).mul hC)).mul hG) ?_
  simp only [smul_eq_mul, OmB]
  have hpos : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t, 2 * (uTop S i : ℕ) + 1 < 2 * s + 1 := by
    intro i
    have := (uTop S i).isLt
    omega
  have hu : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      2 * (uTop S i : ℕ) + 1 < ((⟨2 * s, by omega⟩ : Fin (2 * s + 1)) : ℕ) := by
    intro i
    have := (uTop S i).isLt
    show _ < 2 * s
    omega
  have hdis : ∀ i i' : Fin (blockData p S aTop aPlus mm b).T.t, i ≠ i' →
      2 * (uTop S i : ℕ) ≠ 2 * (uTop S i' : ℕ) ∧ 2 * (uTop S i : ℕ) ≠ 2 * (uTop S i' : ℕ) + 1 ∧
        2 * (uTop S i : ℕ) + 1 ≠ 2 * (uTop S i' : ℕ) := by
    intro i i' h
    have hv : (i : ℕ) ≠ i' := fun e => h (Fin.ext e)
    have e1 : (uTop S i : ℕ) = S.sigma + i := rfl
    have e2 : (uTop S i' : ℕ) = S.sigma + i' := rfl
    omega
  have hj : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      jl i ≤ (segChain p S aTop b).deg ⟨2 * (uTop S i : ℕ), by have := hpos i; omega⟩ ∧
        jl i ≤ (segChain p S aTop b).deg ⟨2 * (uTop S i : ℕ) + 1, hpos i⟩ := by
    intro i
    obtain ⟨a1, a2⟩ := hlev.1 i
    have hu' := (uTop S i).isLt
    have e1 : (blockData p S aTop aPlus mm b).letterAt ((blockData p S aTop aPlus mm b).T.pos i)
        = ⟨2 * (uTop S i : ℕ), by omega⟩ :=
      Fin.ext (by show min (2 * (uTop S i : ℕ)) (2 * s + 1 - 1) = 2 * (uTop S i : ℕ); omega)
    have e2 : (blockData p S aTop aPlus mm b).letterAt ((blockData p S aTop aPlus mm b).T.pos i + 1)
        = ⟨2 * (uTop S i : ℕ) + 1, by omega⟩ :=
      Fin.ext (by show min (2 * (uTop S i : ℕ) + 1) (2 * s + 1 - 1) = 2 * (uTop S i : ℕ) + 1; omega)
    rw [e1] at a1
    rw [e2] at a2
    exact ⟨a1, a2⟩
  have hjp : jp ≤ (segChain p S aTop b).deg ⟨2 * s, by omega⟩ := (le_min_iff.mp hlev.2).1
  have hBj : jp ≤ (blockData p S aTop aPlus mm b).B := (le_min_iff.mp hlev.2).2
  have hk := gen_wh_of_pos_separated_of_le_deg (segChain p S aTop b).deg
    (fun l : Fin (blockData p S aTop aPlus mm b).T.t => 2 * (uTop S l : ℕ)) jl ⟨2 * s, by omega⟩ jp
    (fun a => ωL a.castSucc) hpos hu hdis hj hjp
  beta_reduce at hk
  have hf : ∀ k (hk' : k < 2 * s + 1), finPos (2 * s + 1) k = Fin.castSucc ⟨k, hk'⟩ := by
    intro k hk'
    exact Fin.ext (by show min k (2 * s + 1) = k; omega)
  have eE : ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      jl x * (ωL (finPos (2 * s + 1) (2 * ↑(uTop S x))) + ωL (finPos (2 * s + 1) (2 * ↑(uTop S x) + 1)))
      = ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      jl x * (ωL (Fin.castSucc ⟨2 * (uTop S x : ℕ), by have := hpos x; omega⟩)
        + ωL (Fin.castSucc ⟨2 * (uTop S x : ℕ) + 1, hpos x⟩)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hf _ (by have := hpos x; omega), hf _ (hpos x)]
  have eL : ∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL a.castSucc
      = ∑ a : Fin (2 * s + 1), (((segChain p S aTop b).deg a - ∑ i : Fin (blockData p S aTop aPlus mm b).T.t,
        if (a : ℕ) = 2 * (uTop S i : ℕ) ∨ (a : ℕ) = 2 * (uTop S i : ℕ) + 1 then jl i else 0)
        - if a = ⟨2 * s, by omega⟩ then jp else 0) * ωL a.castSucc := rfl
  have eZ : ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      (blockData p S aTop aPlus mm b).T.z x * ω (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t x.castSucc)
      = ∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (l.castSucc, false)) := rfl
  have eZl : (blockData p S aTop aPlus mm b).zPlus *
      ω (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.last (blockData p S aTop aPlus mm b).T.t))
      = (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) := rfl
  have eB : (blockData p S aTop aPlus mm b).B = S.bPlus := rfl
  rw [eE, eZ, eZl, eL, ← hk]
  rw [eB] at hBj
  rw [eB]
  obtain ⟨k, hk2⟩ := Nat.exists_eq_add_of_le hBj
  rw [hk2, Nat.add_sub_cancel_left]
  ring

end Gen

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IM (X : Loc) := (Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕
  ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j) × Fin X.m) ⊕ ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕ Fin X.m))

def multMk (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inl x => (β x.1).sg x.2
  | Sum.inr (Sum.inl x) => (β x.1).rz x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => (β x.1).ry x.2 0
  | Sum.inr (Sum.inr (Sum.inr _)) => X.c

def fMk (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → RHH O X
  | Sum.inl x => kSkey O X x.1 x.2 ^ (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl x) => kWkey O X x.1 x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => kSkey O X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr c)) => locC O X c.succ

def aMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → MonH X
  | Sum.inl x => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
  | Sum.inr (Sum.inl x) => Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)
  | Sum.inr (Sum.inr (Sum.inl x)) => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ j : Fin (numSeg X.TT), Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)

def oMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → ℕ
  | Sum.inl x => (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def dgMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → X.TT × Bool → ℕ
  | Sum.inl x => fun l => (X.seg C0 CE1 CE2 x.1).P X.p x.2 * dgKS X x.1 x.2 l
  | Sum.inr (Sum.inl x) => dgKW X x.1 x.2.1
  | Sum.inr (Sum.inr (Sum.inl x)) => dgKS X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr _)) => dgLoc X

def bMk (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1))) +
    (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

end Formalism.MainNotions.ColumnSystems.Pf
