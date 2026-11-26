module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

def pairSet {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) :
    Set ((Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ)) :=
  {x | IsPair A Ai Ci x.1 x.2}

theorem pairSet_finite (hCD : ChainDimAt) {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) : (pairSet r A Ai Ci).Finite := by
  classical
  have hc := chains_finite (r := r) hCD (kLetters A Ai Ci)
  have hl : (⋃ mu ∈ {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ | IsChain (kLetters A Ai Ci) mu},
      Set.Icc (fun i : Fin r => mu (Fin.last _) i.succ) (fun i : Fin r => mu (Fin.last _) i.castSucc)).Finite :=
    hc.biUnion fun mu _ => Set.finite_Icc _ _
  refine (hc.prod hl).subset ?_
  intro t ht
  refine ⟨ht.1, ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨t.1, ht.1, fun i => (ht.2 i).1, fun i => (ht.2 i).2⟩

theorem tl_symDim_nat (m g : ℕ) : symDim (m + 1) (g : ℤ) = sd m g := by
  unfold symDim sd
  rw [if_neg (by omega)]
  simp


open Classical in
theorem pair_sum (hCD : ChainDimAt) (hNB : NumBranchAt) {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) :
    ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, wdim x.2 = (dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) := by
  have e0 : ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, wdim x.2 =
      ∑ᶠ x : (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ), if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0 := by
    rw [finsum_eq_sum_of_support_subset (s := (pairSet_finite hCD r A Ai Ci).toFinset)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      have : IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hx
      rw [if_pos this]
    · intro x hx
      by_contra hn
      apply hx
      have : ¬ IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hn
      show (if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
      rw [if_neg this]
  have hfin : (support fun x : (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ) =>
      if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0).Finite := by
    refine (pairSet_finite hCD r A Ai Ci).subset fun x hx => ?_
    by_contra hn
    apply hx
    have : ¬ IsPair A Ai Ci x.1 x.2 := hn
    show (if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
    rw [if_neg this]
  rw [e0, finsum_curry _ hfin]
  have e1 : (dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) = ∏ a, (sdXi (r + 1) ((kLetters A Ai Ci).deg a) : ℚ) := by
    rw [prod_kLetters]
    unfold dimMM
    simp only [tl_symDim_nat]
    push_cast
    rfl
  rw [e1, ← hCD (2 * s + 1) (r + 1) (kLetters A Ai Ci)]
  unfold chainSum
  refine finsum_congr fun mu => ?_
  by_cases hmu : IsChain (kLetters A Ai Ci) mu
  · rw [if_pos ⟨hmu, fun k => k.elim0⟩, hNB r _ (IsChain.anti_last hmu)]
    refine finsum_congr fun lam => ?_
    by_cases hl : Inter (mu (Fin.last _)) lam
    · have hl' : ∀ i : Fin r, mu (Fin.last _) i.succ ≤ lam i ∧ lam i ≤ mu (Fin.last _) i.castSucc := hl
      rw [if_pos hl', if_pos (show IsPair A Ai Ci mu lam from ⟨hmu, hl⟩)]
    · have hl' : ¬ ∀ i : Fin r, mu (Fin.last _) i.succ ≤ lam i ∧ lam i ≤ mu (Fin.last _) i.castSucc := hl
      rw [if_neg hl', if_neg (show ¬ IsPair A Ai Ci mu lam from fun h => hl h.2)]
  · rw [if_neg (fun h => hmu h.1)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro lam
    rw [if_neg (show ¬ IsPair A Ai Ci mu lam from fun h => hmu h.1)]

open Classical in
theorem kept_sum (hCD : ChainDimAt) (p : ℕ) (La : ℝ) {s : ℕ} (r : ℕ) [NeZero r] (A : ℕ) (Ai Ci : Fin s → ℕ) :
    keptPairSum p La (r := r) A Ai Ci =
      ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, if KeptPair p La Ai Ci x.1 x.2 then wdim x.2 else 0 := by
  unfold keptPairSum
  rw [finsum_eq_sum_of_support_subset (s := (pairSet_finite hCD r A Ai Ci).toFinset)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have : IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hx
    by_cases hk : KeptPair p La Ai Ci x.1 x.2
    · rw [if_pos ⟨this, hk⟩, if_pos hk]
    · rw [if_neg (fun h => hk h.2), if_neg hk]
  · intro x hx
    by_contra hn
    apply hx
    have : ¬ IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hn
    show (if IsPair A Ai Ci x.1 x.2 ∧ KeptPair p La Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
    rw [if_neg (fun h => this h.1)]


open Classical in
theorem tail_core (hCD : ChainDimAt) (hNB : NumBranchAt) (p : ℕ) (La : ℝ) {s : ℕ} (r : ℕ) [NeZero r] (A : ℕ)
    (Ai Ci : Fin s → ℕ) (Np W e : ℝ) (hW : 0 ≤ W)
    (hN : ((pairSet r A Ai Ci).ncard : ℝ) ≤ Np)
    (hwt : ∀ (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ),
      IsPair A Ai Ci mu lam → ¬ KeptPair p La Ai Ci mu lam →
      ((wdim lam : ℚ) : ℝ) ≤ W * (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ))
    (he : Np * W ≤ e) :
    (1 - e) * (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ) ≤ ((keptPairSum p La (r := r) A Ai Ci : ℚ) : ℝ) := by
  set F := (pairSet_finite hCD r A Ai Ci).toFinset with hF
  set M : ℝ := (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have h1 : (∑ x ∈ F, ((wdim x.2 : ℚ) : ℝ)) = M := by
    have := pair_sum hCD hNB r A Ai Ci
    have h2 : ((∑ x ∈ F, wdim x.2 : ℚ) : ℝ) = ((dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) : ℝ) := by rw [hF, this]
    push_cast at h2
    exact h2
  have h2 : ((keptPairSum p La (r := r) A Ai Ci : ℚ) : ℝ) =
      ∑ x ∈ F, if KeptPair p La Ai Ci x.1 x.2 then ((wdim x.2 : ℚ) : ℝ) else 0 := by
    rw [kept_sum hCD]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h3 : ∀ x ∈ F, ((wdim x.2 : ℚ) : ℝ) - W * M ≤ if KeptPair p La Ai Ci x.1 x.2 then ((wdim x.2 : ℚ) : ℝ) else 0 := by
    intro x hx
    have hp : IsPair A Ai Ci x.1 x.2 := by simpa [hF, pairSet] using hx
    have hWM : 0 ≤ W * M := mul_nonneg hW hM0
    split_ifs with hk
    · linarith
    · have := hwt x.1 x.2 hp hk
      linarith
  have h4 := Finset.sum_le_sum h3
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, nsmul_eq_mul, ← h2] at h4
  have h5 : (F.card : ℝ) ≤ Np := by
    rw [hF, ← Set.ncard_eq_toFinset_card _ (pairSet_finite hCD r A Ai Ci)]
    exact hN
  have h6 : (F.card : ℝ) * (W * M) ≤ e * M := by
    have : (F.card : ℝ) * W ≤ e := le_trans (mul_le_mul_of_nonneg_right h5 hW) he
    calc (F.card : ℝ) * (W * M) = ((F.card : ℝ) * W) * M := by ring
      _ ≤ e * M := mul_le_mul_of_nonneg_right this hM0
  linarith

theorem tail_num (a k C0 : ℝ) (N1 : ℕ) (ha : 9 ≤ a) (hk0 : 0 ≤ k) (hk : k ≤ a) (hN : 1 ≤ N1) (hC : 880 ≤ C0)
    (hL : 1 ≤ Real.log a) :
    (8 * a) ^ (4 * (N1 + 1) ^ 2) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * Real.log a / 5) * (8 * a + k) ^ ((2 * N1 + 2) ^ 2)) ≤
      Real.exp (-(C0 * (N1 : ℝ) ^ 2 * Real.log a) / 8) := by
  set L := Real.log a with hLdef
  have ha0 : 0 < a := by linarith
  have hE : Real.exp (2 * L) = a ^ 2 := by
    rw [two_mul, Real.exp_add, hLdef, Real.exp_log ha0]; ring
  have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hb1 : 8 * a ≤ Real.exp (2 * L) := by rw [hE]; nlinarith
  have hb2 : 8 * a + k ≤ Real.exp (2 * L) := by rw [hE]; nlinarith
  have hn1 : 4 * (N1 + 1) ^ 2 ≤ 16 * N1 ^ 2 := by nlinarith
  have hn2 : (2 * N1 + 2) ^ 2 ≤ 16 * N1 ^ 2 := by nlinarith
  have p1 : (8 * a) ^ (4 * (N1 + 1) ^ 2) ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) := by
    rw [Real.exp_nat_mul]
    exact le_trans (pow_le_pow_left₀ (by linarith) hb1 _) (pow_le_pow_right₀ hE1 hn1)
  have p2 : (8 * a + k) ^ ((2 * N1 + 2) ^ 2) ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) := by
    rw [Real.exp_nat_mul]
    exact le_trans (pow_le_pow_left₀ (by linarith) hb2 _) (pow_le_pow_right₀ hE1 hn2)
  have hN1 : (1 : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast hN
  have hNL : 1 ≤ (N1 : ℝ) ^ 2 * L := by nlinarith [mul_self_nonneg ((N1 : ℝ) - 1)]
  calc (8 * a) ^ (4 * (N1 + 1) ^ 2) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * L / 5) * (8 * a + k) ^ ((2 * N1 + 2) ^ 2))
      ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * L / 5) * Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L))) := by
        apply mul_le_mul p1 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left p2 (Real.exp_pos _).le
    _ = Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L) + (2 - C0 * (N1 : ℝ) ^ 2 * L / 5 +
          ((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L))) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(C0 * (N1 : ℝ) ^ 2 * L) / 8) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have : 880 * ((N1 : ℝ) ^ 2 * L) ≤ C0 * ((N1 : ℝ) ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hC (by linarith)
        nlinarith

def PairCountAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ((pairSet X.m A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)).ncard : ℝ) ≤
          (8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2)

def NotKeptWtAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ mu lam, IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ¬ KeptPair X.p (X.La C0) (r := X.m) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ((wdim lam : ℚ) : ℝ) ≤ Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) *
            (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ)

def RestPairCount : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairCountAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestNotKeptWt : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem threshold_standard_large : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => 880 ≤ C0 ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 880) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 h880 h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨h880, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem tail_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hCD : ChainDimAt) (hNB : NumBranchAt) (h880 : 880 ≤ C0)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hP : PairCountAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hW : NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2
  have S := hstd X hD hI hc
  have hk5 := S.k5
  have hkQ := S.kQ le_rfl
  have hQ1 := S.Q1
  have hkb := S.kb
  have hb1 : 1 ≤ X.b' := by nlinarith [pow_pos (show (0 : ℝ) < X.k by linarith) 3, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hk5 3]
  have hka : X.k ≤ X.a := le_trans (le_mul_of_one_le_right (by linarith) hb1) hkb
  have hb9 : 9 ≤ X.b' := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hk5 3]
  have ha9 : (9 : ℝ) ≤ X.a := le_trans hb9 S.ba
  have hnum := tail_num X.a X.k C0 X.N1 ha9 (by linarith) hka S.N1pos h880 S.loga
  have hLa : X.La C0 = C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a := rfl
  refine tail_core hCD hNB X.p (X.La C0) X.m A _ _ ((8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2))
    (Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2)) _ (by positivity)
    (hP X hD hI hc j rz ry hd A hA1 hA2) (hW X hD hI hc j rz ry hd A hA1 hA2) ?_
  rw [hLa]
  exact hnum

theorem restTail_of (hCD : ChainDimAt) (hNB : NumBranchAt) (hP : RestPairCount) (hW : RestNotKeptWt) : RestTail := by
  refine TransportedAlt.mono ?_ ((threshold_standard_large.and hP).and hW)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨h880, hstd⟩, hp⟩, hw⟩
  exact tail_of hCD hNB h880 hstd hp hw

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RestCountUpOfSTop
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem floor_sub_le (x : ℤ) {m : ℝ} (hm : 0 ≤ m) : ⌊(x : ℝ) - m⌋ ≤ x := by
  have h := Int.floor_mono (sub_le_self (x : ℝ) hm)
  rwa [Int.floor_intCast] at h

theorem thr_U [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m) (b : SegBlock s r)
    (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) (i : Fin s)
    (hi : S.sigma ≤ i.val) : ka ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap p S b i.val := by
  have hit : i.val - S.sigma < S.t := by unfold SegData.t; have := i.2; omega
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = i.val - S.sigma :=
    ⟨⟨i.val - S.sigma, by show i.val - S.sigma < S.t + 1; omega⟩, rfl⟩
  have hkt : k.val < S.t := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * i.val + 1
    rw [dite_eq_left hkt]
    show min (2 * (S.sigma + k.val) + 1) (2 * s + 1) = 2 * i.val + 1
    omega
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b i.val : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dite_eq_left hkt, WithTop.map_coe]
    have hu : ((uTop S ⟨k.val, hkt⟩ : Fin s) : ℕ) = i.val := by
      show S.sigma + k.val = i.val
      omega
    rw [hu]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

theorem thr_last [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (b : SegBlock s r) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) :
    ka (Fin.last _) 0 ≤ cap p S b s := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = S.t :=
    ⟨⟨S.t, by show S.t < S.t + 1; omega⟩, rfl⟩
  have hkt : ¬ (k.val < S.t) := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = Fin.last _ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * s + 1
    rw [dite_eq_right hkt]
    exact min_self _
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dite_eq_right hkt, WithTop.map_coe]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

def STopRowsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 i.val ∧
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 (i.val + 1)

theorem firstRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hS : STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FirstRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold FirstRowsAt
  intro X _ hD hI hc j m hm rz ry hdig z hz
  have hS' := hS X hD hI hc j m hm rz ry hdig z hz
  obtain ⟨b, ⟨jl, jp⟩, ka⟩ := z
  obtain ⟨⟨hK, -, -⟩, -, -, hok⟩ := hz
  dsimp only at hS' hK hok ⊢
  refine ⟨fun i c hc0 => ?_, fun c hc0 => ?_⟩
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
    · exact hS' i hi
    · have h1 := thr_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok i
        (by omega)
      refine ⟨h1, ?_⟩
      rw [cap_succ]
      have h2 := (hK.2.1 i (by omega)).1
      have h3 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := by
        unfold oEff
        rw [if_neg hi]
      omega
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    exact thr_last X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok

def RestSTopRows : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restFirstRows_of (h : RestSTopRows) : RestFirstRows := by
  unfold RestSTopRows TransportedAlt at h
  unfold RestFirstRows TransportedAlt
  intro Cc hCc
  obtain ⟨U0, hU0, h0⟩ := h Cc hCc
  refine ⟨U0, hU0, fun C0 hC0 => ?_⟩
  obtain ⟨U1, hU1, h1⟩ := h0 C0 hC0
  refine ⟨U1, hU1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨U2, hU2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  exact ⟨U2, hU2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => firstRows_of (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

theorem restCountUp_of_STop (hCD : ChainDimAt) (hNB : NumBranchAt) (h : RestSTopRows) : RestCountUp := restCountUp_of_rows hCD hNB (restFirstRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem strip_first [NeZero r] {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : nu 0 ≤ mu 0 + g := by
  obtain ⟨h1, -, h3⟩ := h
  have hs : ∑ i, (nu i - mu i) = g := by
    rw [Finset.sum_sub_distrib]
    exact h3
  have h0 := Finset.single_le_sum (f := fun i => nu i - mu i) (fun i _ => sub_nonneg.mpr (h1 i))
    (Finset.mem_univ (0 : Fin r))
  linarith

theorem sum_lt_succ (f : Fin s → ℤ) (i : Fin s) :
    (∑ x : Fin s, if x.val < i.val + 1 then f x else 0) = (∑ x : Fin s, if x.val < i.val then f x else 0) + f i := by
  have hpt : ∀ x : Fin s, (if x.val < i.val + 1 then f x else 0) =
      (if x.val < i.val then f x else 0) + (if x = i then f x else 0) := by
    intro x
    by_cases h1 : x.val < i.val
    · have h2 : x ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h5 : x.val < i.val + 1 := by omega
      simp [h1, h2, h5]
    · by_cases h3 : x = i
      · subst h3
        simp
      · have h4 : ¬ x.val < i.val + 1 := by
          intro h
          apply h3
          apply Fin.ext
          omega
        simp [h1, h3, h4]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem eventually_abs_le_half_add_of_doubling_bounds [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (m : ℕ) (hm : m < 2 * s + 1) :
    ka ⟨m + 1, by omega⟩ 0 ≤ ka ⟨m, by omega⟩ 0 + (if m % 2 = 0 then (LLv.deg ⟨m, hm⟩ : ℤ) else 0) := by
  have h := hch.2 ⟨m, hm⟩
  have e1 : (⟨m, hm⟩ : Fin (2 * s + 1)).succ = ⟨m + 1, by omega⟩ := rfl
  have e2 : (⟨m, hm⟩ : Fin (2 * s + 1)).castSucc = ⟨m, by omega⟩ := rfl
  rw [e1, e2, hv] at h
  by_cases hpar : m % 2 = 0
  · simp [hpar] at h ⊢
    exact strip_first h
  · simp [hpar] at h ⊢
    exact h.1 0

theorem row_even [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) :
    ∀ (n : ℕ) (hn : n ≤ s), ka ⟨2 * n, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro hn
    have h0 : ka ⟨2 * 0, by omega⟩ = 0 := hch.1
    rw [h0]
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hs1 := hch.2 ⟨2 * n, by omega⟩
    rw [if_pos (by rw [hv]; simp)] at hs1
    have hs2 := hch.2 ⟨2 * n + 1, by omega⟩
    rw [if_neg (by rw [hv]; simp)] at hs2
    have a1 : ka ⟨2 * n + 1, by omega⟩ 0 ≤ ka ⟨2 * n, by omega⟩ 0 + (LLv.deg ⟨2 * n, by omega⟩ : ℤ) := strip_first hs1
    have a2 : ka ⟨2 * (n + 1), by omega⟩ 0 ≤ ka ⟨2 * n + 1, by omega⟩ 0 := hs2.1 0
    have hsum : (∑ l : Fin s, if l.val < n + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
        (∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
          (LLv.deg ⟨2 * n, by omega⟩ : ℤ) :=
      sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) ⟨n, by omega⟩
    rw [hsum]
    linarith

theorem row_odd [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (i : Fin s) :
    ka ⟨2 * i.val + 1, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  have h1 := eventually_abs_le_half_add_of_doubling_bounds hv hch (2 * i.val) (by omega)
  rw [if_pos (by omega)] at h1
  have h3 := row_even hv hch i.val (by omega)
  have hsum : (∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      (∑ l : Fin s, if l.val < i.val then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
        (LLv.deg ⟨2 * i.val, by omega⟩ : ℤ) :=
    sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) i
  rw [hsum]
  linarith

def SecondKernelAtLevel (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b i.val ∧
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b (i.val + 1)

theorem sTopRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hK : SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm rz ry hd z hz i hi
  have h1 := row_odd (LLv := (BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) (fun a => rfl) hz.2.2.1 i
  have e : (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then
        (((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2).deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      ∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (z.1.w l : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl, if_pos hl, levW, if_pos (by omega), jE_S _ _ (by omega), Nat.sub_zero]
    · rw [if_neg hl, if_neg hl]
  rw [e] at h1
  have h2 := hK X hD hH hc j z.1 hz.1.1 i hi
  exact ⟨le_trans h1 h2.1, le_trans h1 h2.2⟩

def LeadingRowsBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restSTopRows_of (h : LeadingRowsBeyondThreshold) : RestSTopRows :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ hK => sTopRows_of hK) h

theorem upper_count_of_top_rows (hCD : ChainDimAt) (hNB : NumBranchAt) (h : LeadingRowsBeyondThreshold) : RestCountUp :=
  restCountUp_of_STop hCD hNB (restSTopRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  have hl : i = Fin.last m → j = Fin.last m := fun hi => le_antisymm (Fin.le_last j) (hi ▸ hij)
  have h0 : j = 0 → i = 0 := fun hj => le_antisymm (hj ▸ hij) (Fin.zero_le i)
  unfold letterWt
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : j = Fin.last m
    · by_cases hi : i = Fin.last m
      · simp [hi, hj]
      · simp [hi, hj]
    · have hi : i ≠ Fin.last m := fun hi => hj (hl hi)
      simp [hi, hj]
  · simp only [if_true]
    by_cases hj : j = 0
    · simp [hj, h0 hj]
    · by_cases hi : i = 0
      · simp [hi, hj]
      · simp [hi, hj]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.MapFloorMono
section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SrcHalf
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def MonoAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p r : ℕ) [NeZero r] {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (b : SegBlock s r) (m m' : ℝ), m ≤ m' →
    (blockData p S aTop aPlus m' b).SSZ O (r := r) ≤ (blockData p S aTop aPlus m b).SSZ O (r := r)

def PlaneAt : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (m : ℕ) (φ : WF p n' ≃+* W) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e e' : Edge W Qq (m + 1)), IsFractionRing W Qq →
    IsGLW g → IsGLW g' → IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    IsEdgeBasis p 1 e' (h * ((matQ φ g')⁻¹).transpose) → ratPlane p n' 1 g' = ratPlane p n' 1 g → e' = e

def SymIntAt (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
    (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)).SSZ O
      (r := X.m)) →
    InA (O := O) (symFam (KK O) X.p C0 CE1 CE2 X β s)

theorem scale_one_mem {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {M : Submodule O V} {x : V} (hx : x ∈ scale (1 : Kf) M) : x ∈ M := by
  simp only [scale, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end
