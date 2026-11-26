module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LDigits
section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementL
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

section Digits

variable {I1 I2 : Type}

end Digits

section Residue

def cnt (T Q r c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin T)).filter (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card

lemma shift_iff (Q a s c : ℕ) (hQ : 1 ≤ Q) :
    (a + s) % Q = c % Q ↔ s % Q = (c + (Q - 1) * a) % Q := by
  obtain ⟨R, rfl⟩ : ∃ R, Q = R + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    have h0 : Nat.ModEq (R + 1) (a + s) c := h
    have h1 : Nat.ModEq (R + 1) (a + s + R * a) (c + R * a) := h0.add_right (R * a)
    have h2 : a + s + R * a = s + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (s + (R + 1) * a) % (R + 1) = (c + R * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3
  · intro h
    have h0 : Nat.ModEq (R + 1) s (c + R * a) := h
    have h1 : Nat.ModEq (R + 1) (a + s) (a + (c + R * a)) := h0.add_left a
    have h2 : a + (c + R * a) = c + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (a + s) % (R + 1) = (c + (R + 1) * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3

lemma cnt_succ (T Q r c : ℕ) (hQ : 1 ≤ Q) :
    cnt T Q (r + 1) c = ∑ a : Fin T, cnt T Q r (c + (Q - 1) * a) := by
  have hbij : Function.Bijective
      (fun p : Fin T × (Fin r → Fin T) => (Fin.cons p.1 p.2 : Fin (r + 1) → Fin T)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => (u 0, Fin.tail u), fun p => ?_, fun u => ?_⟩
    · simp
    · simp
  simp only [cnt, Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact if_congr (shift_iff _ _ _ _ hQ).symm rfl rfl

lemma cnt_one (T Q c : ℕ) (hT : T ≤ Q) : cnt T Q 1 c = if c % Q < T then 1 else 0 := by
  have hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
  have step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) =
      ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0 := by
    symm
    refine Fintype.sum_bijective _ hbij _ _ (fun a => ?_)
    simp only [Fin.sum_univ_one]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]
  unfold cnt
  rw [Finset.card_filter, step]
  by_cases h : c % Q < T
  · rw [if_pos h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      exact if_neg (fun e => hb (Fin.ext e))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun e => h (lt_of_eq_of_lt e.symm a.isLt))

private theorem eq_of_add_pred_mul_mod_eq_of_lt (Q c a b : ℕ) (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (h : (c + (Q - 1) * a) % Q = (c + (Q - 1) * b) % Q) : a = b := by
  have h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)
  have h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])
  have h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q) :=
    h1.trans h2.symm
  have h4 : Nat.ModEq Q a b := Nat.ModEq.add_right_cancel' _ h3
  have h5 : a % Q = b % Q := h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h5

lemma cnt_two (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by
  have h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a) :=
    cnt_succ T Q 1 c hQ
  rw [h2]
  simp only [cnt_one T Q _ hT]
  have hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
      ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
        (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1 := by
      intro a
      by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hle : ((Finset.univ : Finset (Fin T)).filter
      (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T := by
    have hc : ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)
      · intro a ha
        have ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q := by simpa using ha
        simp only [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨ha', Nat.mod_lt _ (by omega)⟩
      · intro a _ b _ hab
        exact Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT)
          (lt_of_lt_of_le b.isLt hT) hab)
    rw [Nat.card_Ico] at hc
    exact hc
  omega

lemma cnt_ge (T Q : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) (s : ℕ) :
    ∀ c, T ^ s * (T - (Q - T)) ≤ cnt T Q (s + 2) c := by
  induction s with
  | zero =>
    intro c
    rw [pow_zero, one_mul]
    exact cnt_two T Q c hQ hT
  | succ s ih =>
    intro c
    rw [show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]
    calc T ^ (s + 1) * (T - (Q - T)) = ∑ _a : Fin T, T ^ s * (T - (Q - T)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) :=
          Finset.sum_le_sum (fun a _ => ih _)

private theorem pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (q b : ℝ) (hb : 0 ≤ b) (hbq : b ≤ q) :
    ∀ m : ℕ, q ^ m * (q - ((m : ℝ) + 2) * b) ≤ (q - b) ^ m * (q - 2 * b) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hq : 0 ≤ q := le_trans hb hbq
    have h1 : (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : 0 ≤ q ^ m * (((m : ℝ) + 2) * b ^ 2) :=
      mul_nonneg (pow_nonneg hq m) (by positivity)
    calc q ^ (m + 1) * (q - (((m + 1 : ℕ) : ℝ) + 2) * b)
        = (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) - q ^ m * (((m : ℝ) + 2) * b ^ 2) := by
          push_cast
          ring
      _ ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) := by linarith
      _ = (q - b) ^ (m + 1) * (q - 2 * b) := by ring

theorem residueClassLowerBound : ResidueClassLowerBound := by
  intro r Q be c hr hQ
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have key := cnt_ge (Q - 2 * be) Q (by omega) (by omega) m c
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  refine le_trans ?_ key'
  have eq1 : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
      (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) := by
    have h : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
        (Q : ℝ) ^ m * (Q : ℝ) - (Q : ℝ) ^ m * (((m : ℝ) + 2) * (2 * (be : ℝ))) * ((Q : ℝ) / (Q : ℝ)) := by
      push_cast
      ring
    rw [h, div_self hQne, mul_one]
    ring
  rw [show m + 2 - 1 = m + 1 by omega]
  refine le_trans (le_of_eq eq1) ?_
  by_cases h4 : 2 * (2 * be) ≤ Q
  · have e1 : (Q - 2 * be) - (Q - (Q - 2 * be)) = Q - 2 * (2 * be) := by omega
    have c1 : ((Q - 2 * be : ℕ) : ℝ) = (Q : ℝ) - 2 * (be : ℝ) := by
      rw [Nat.cast_sub (show 2 * be ≤ Q by omega)] <;> push_cast <;> ring
    have c2 : ((Q - 2 * (2 * be) : ℕ) : ℝ) = (Q : ℝ) - 2 * (2 * (be : ℝ)) := by
      rw [Nat.cast_sub h4] <;> push_cast <;> ring
    rw [Nat.cast_mul, Nat.cast_pow, e1, c1, c2]
    exact pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (Q : ℝ) (2 * (be : ℝ)) (by positivity) (by exact_mod_cast hQ.le) m
  · have hneg : (Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)) ≤ 0 := by
      have h1 : (Q : ℝ) ≤ 2 * (2 * (be : ℝ)) := by
        exact_mod_cast (show Q ≤ 2 * (2 * be) by omega)
      have h2 : (0 : ℝ) ≤ (m : ℝ) * (be : ℝ) := by positivity
      nlinarith
    have hp : (0 : ℝ) ≤ (Q : ℝ) ^ m := by positivity
    have hle : (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) ≤ 0 := by
      nlinarith [mul_nonneg hp (neg_nonneg.mpr hneg)]
    exact le_trans hle (Nat.cast_nonneg _)

end Residue

section Exact

end Exact

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def BetaRatioBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → 4 * X.Y * (X.beS p K j (X.restr j b) : ℝ) ≤ (X.Qc p K j : ℝ)

def TauDegreeOnPathBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) (dd : Fin (segN X.F j) → ℕ),
      X.IsPATH p K j b μ dd → ∀ i, X.F.fr j 0 ≤ segE X.F j i → dd i ≤ 2 * X.beS p K j b

def ResidueClassCount : Prop :=
  ∀ (r Q be c ρ : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card : ℝ)

section Congr

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K]

theorem Bdeg_congr (j : ℤ) {b b' : ℤ → ℕ} (x : ℤ) (h : b x = b' x) : X.Bdeg p K j b x = X.Bdeg p K j b' x := by
  unfold Dat.Bdeg
  rw [h]

theorem beS_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x) :
    X.beS p K j b = X.beS p K j b' := by
  unfold Dat.beS
  refine Finset.sum_congr rfl fun x hx => ?_
  exact Bdeg_congr X p K j x (h x (Finset.mem_filter.mp hx).2)

theorem IsPATH_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} {dd : Fin (segN X.F j) → ℕ} (hP : X.IsPATH p K j b μ dd) :
    X.IsPATH p K j b' μ dd :=
  ⟨hP.path, fun i hi => by rw [hP.degs i hi]; exact Bdeg_congr X p K j _ (h _ hi),
    fun i i' hi m hm => by rw [hP.head i i' hi m hm, beS_congr X p K j h]⟩

theorem IsGood_congr (hX : X.Hyp p K) (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} (hG : X.IsGood p K j b μ) : X.IsGood p K j b' μ := by
  classical
  intro i hi
  have hlate : segE X.F j i ∈ X.toLate j := Finset.mem_filter.mpr ⟨segE_mem X.F j i, hi⟩
  have hold := (oldest_letter_in_segment p n' r K X hX j _ hlate).2
  have hth : X.thc p K j b' (segE X.F j i) = X.thc p K j b (segE X.F j i) := by
    unfold Dat.thc
    split_ifs with hW
    · rfl
    · have hLL := hold hW
      unfold Frames.LLset at hLL
      have hlt := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hLL).1).2
      rw [h _ hlt]
  rw [hth]
  exact hG i hi

theorem restr_setTau_low (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (x : ℤ) (hx : x < X.F.fr j 0) :
    X.restr j b x = X.restr j (X.setTau j b e) x := by
  unfold Dat.restr Dat.setTau
  have : ¬ (X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1)) := fun h => by omega
  simp only [this, if_false]

theorem restr_setTau_tau (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (i' : Fin r) :
    X.restr j (X.setTau j b e) (X.F.fr j i'.val) = e i' := by
  classical
  have hV := hX.valid
  have hmem := k_fr_mem_letters X.F hV j i'.isLt
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have a2 := kfr_le X.F hV j (Nat.zero_le i'.val) i'.isLt
  have a3 := kfr_le X.F hV j (by have := i'.isLt; omega : i'.val ≤ r - 1) (by have := i'.isLt; omega)
  have hlate : X.F.fr j i'.val ∈ X.toLate j := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    unfold Frames.IsW
    omega
  unfold Dat.restr Dat.setTau
  rw [if_pos hlate, if_pos ⟨a2, a3⟩, Finset.sum_eq_single i']
  · simp
  · intro i _ hne
    rw [if_neg]
    intro h
    exact hne (fr_injective X.F hV j h).symm
  · intro h; exact absurd (Finset.mem_univ _) h

end Congr

theorem restMon_of (C₀ : ℝ) (h61 : BetaRatioBound C₀) (h21 : TauDegreeOnPathBound) (h63 : ResidueClassCount) : RestMon C₀ := by
  intro p n' r K _ _ _ X hX hLa hk j b hA hfin ρ
  classical
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hY : (1 : ℝ) ≤ X.Y := hX.Y1
  have hrhs : (0 : ℝ) ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
        (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rcases le_or_gt (1 - (r : ℝ) / (2 * X.Y)) 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero, zero_pow hr.ne', mul_zero]
    exact hrhs
  rw [max_eq_right hpos.le]
  set be := X.beS p K j (X.restr j b) with hbe
  set Q := X.Qc p K j with hQ
  have hQpos : 0 < Q := by
    rw [hQ]; unfold Dat.Qc
    exact pow_pos hX.prime.pos _
  have hbeQ : 4 * X.Y * (be : ℝ) ≤ (Q : ℝ) := h61 p n' r K X hX hLa hk j b hA
  have hbeQ' : 4 * be ≤ Q := by
    have : (4 : ℝ) * (be : ℝ) ≤ (Q : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) be]
    exact_mod_cast this
  obtain ⟨T, hT⟩ : ∃ T, Q = T + 2 * be := ⟨Q - 2 * be, by omega⟩
  have hTpos : 0 < T := by omega
  have hrN := k_r_le_segN X.F hV hr j
  let idxT : Fin r → Fin (segN X.F j) := fun i' => ⟨segN X.F j - r + i'.val, by have := i'.isLt; omega⟩
  have hidx : ∀ i', segE X.F j (idxT i') = X.F.fr j i'.val := fun i' =>
    (segE_eq_fr_iff X.F hV j _ i'.isLt).mpr rfl
  have := Fintype.ofFinite (X.Tset p K j (X.restr j b))
  let ddOf : X.Tset p K j (X.restr j b) → Fin (segN X.F j) → ℕ := fun τ => Classical.choose τ.2
  have hdd : ∀ τ : X.Tset p K j (X.restr j b), X.IsPATH p K j (X.restr j b) τ.1.1 (ddOf τ) ∧
      X.IsGood p K j (X.restr j b) τ.1.1 ∧ IsSt (tanPart τ.1.1) τ.1.2 := fun τ => Classical.choose_spec τ.2
  let dtau : X.Tset p K j (X.restr j b) → Fin r → ℕ := fun τ i' => ddOf τ (idxT i')
  have hdtau : ∀ τ i', dtau τ i' ≤ 2 * be := by
    intro τ i'
    refine h21 p n' r K X hX j _ _ _ (hdd τ).1 (idxT i') ?_
    rw [hidx]
    exact kfr_le X.F hV j (Nat.zero_le _) i'.isLt
  let Wfin : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range T
  let Ufin : Finset (Fin r × Fin r → ℕ) := Fintype.piFinset fun _ : Fin r × Fin r => Finset.range T
  let φ : X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ) → Fin r → ℕ := fun x i' =>
    dtau x.1 i' + ∑ c, x.2 (i', c)
  let A : Finset (X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ)) :=
    ((Finset.univ : Finset (X.Tset p K j (X.restr j b))) ×ˢ Ufin).filter fun x => ∀ i', φ x i' % Q = ρ i' % Q
  set E := Fintype.piFinset fun i : Fin r => (Finset.range (r * Q)).filter fun e => e % Q = ρ i % Q with hE
  set cst : ℝ := (Q : ℝ) ^ (r - 1) * (1 - (r : ℝ) / (2 * X.Y)) with hcst
  have hcst0 : 0 ≤ cst := by positivity

  have hφE : ∀ x ∈ A, φ x ∈ E := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hu := (Finset.mem_product.mp hx1).2
    rw [Fintype.mem_piFinset] at hu
    rw [hE, Fintype.mem_piFinset]
    intro i'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hx2 i'⟩
    have h1 : ∑ c, x.2 (i', c) ≤ r * (T - 1) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin r)) (fun c => x.2 (i', c)) (T - 1) (by
        intro c _
        have := Finset.mem_range.mp (hu (i', c))
        omega)
      simpa using this
    have h2 := hdtau x.1 i'
    have h3 : r * (T - 1) + r = r * T := by
      obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have h4 : 2 * be ≤ r * (2 * be) := Nat.le_mul_of_pos_left _ hr
    have h5 : r * Q = r * T + r * (2 * be) := by rw [hT]; ring
    show dtau x.1 i' + ∑ c, x.2 (i', c) < r * Q
    omega

  have hfib : ∀ e ∈ E, (A.filter fun x => φ x = e).card ≤ Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) := by
    intro e _
    have hlow := restr_setTau_low X j b e
    have hbe' : X.beS p K j (X.restr j (X.setTau j b e)) = be := (beS_congr X p K j hlow).symm
    have hfinI : Finite (X.Idx p K j (X.restr j (X.setTau j b e))) := by
      let g : X.Idx p K j (X.restr j (X.setTau j b e)) →
          X.Tset p K j (X.restr j b) × (Fin r × Fin r → Fin Q) := fun q =>
        (⟨(q.1.1, q.1.2.1), by
          obtain ⟨dd, h1, h2, h3, -⟩ := q.2
          exact ⟨dd, IsPATH_congr X p K j (fun x hx => (hlow x hx).symm) h1,
            IsGood_congr X p K hX j (fun x hx => (hlow x hx).symm) h2, h3⟩⟩,
          fun v => ⟨q.1.2.2 v, by
            obtain ⟨dd, -, -, -, h4, -⟩ := q.2
            have := h4 v
            omega⟩)
      refine Finite.of_injective g ?_
      intro q q' hqq
      have h1 : q.1.1 = q'.1.1 := congrArg (fun z => z.1.1.1) hqq
      have h2 : q.1.2.1 = q'.1.2.1 := congrArg (fun z => z.1.1.2) hqq
      refine Subtype.ext (Prod.ext h1 (Prod.ext h2 ?_))
      funext v
      exact congrArg (fun z => (z.2 v).val) hqq
    let g : {x // x ∈ A.filter fun x => φ x = e} → X.Idx p K j (X.restr j (X.setTau j b e)) := fun x =>
      ⟨(x.1.1.1.1, x.1.1.1.2, x.1.2), by
        obtain ⟨hxA, hxe⟩ := Finset.mem_filter.mp x.2
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hxA
        have hu := (Finset.mem_product.mp hx1).2
        rw [Fintype.mem_piFinset] at hu
        refine ⟨ddOf x.1.1, IsPATH_congr X p K j hlow (hdd x.1.1).1, IsGood_congr X p K hX j hlow (hdd x.1.1).2.1,
          (hdd x.1.1).2.2, ?_, ?_⟩
        · intro v
          rw [hbe']
          have := Finset.mem_range.mp (hu v)
          show x.1.2 v + 2 * be < Q
          omega
        · intro i i' hi
          have hii : i = idxT i' := (segE_strictMono X.F j).injective (hi.trans (hidx i').symm)
          rw [restr_setTau_tau X p K hX j b e i', hii]
          exact congrFun hxe i'⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      have h1 : x.1.1.1.1 = x'.1.1.1.1 := congrArg (fun z => z.1.1) hxx
      have h2 : x.1.1.1.2 = x'.1.1.1.2 := congrArg (fun z => z.1.2.1) hxx
      have h3 : x.1.2 = x'.1.2 := congrArg (fun z => z.1.2.2) hxx
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3)
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

  have hcount : ∀ τ : X.Tset p K j (X.restr j b), cst ^ r ≤ ((A.filter fun x => x.1 = τ).card : ℝ) := by
    intro τ
    have h1 : ∀ i' : Fin r, cst ≤ ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      intro i'
      have h63' := h63 r Q be (dtau τ i') (ρ i') hX.r2 (by omega)
      rw [show Q - 2 * be = T by omega] at h63'
      refine le_trans ?_ h63'
      rw [hcst]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      have hYp : (0 : ℝ) < X.Y := by linarith
      have : 2 * (r : ℝ) * (be : ℝ) / Q ≤ (r : ℝ) / (2 * X.Y) := by
        rw [div_le_div_iff₀ hQr (by positivity)]
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have h2 : (Fintype.piFinset fun i' : Fin r =>
        Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card ≤ (A.filter fun x => x.1 = τ).card := by
      refine Finset.card_le_card_of_injOn (fun w => (τ, fun v : Fin r × Fin r => w v.1 v.2)) ?_ ?_
      · intro w hw
        have hw' := Fintype.mem_piFinset.mp (Finset.mem_coe.mp hw)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun v => ?_⟩, fun i' => ?_⟩, rfl⟩)
        · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hw' v.1)).1 v.2
        · exact (Finset.mem_filter.mp (hw' i')).2
      · intro w _ w' _ hww
        simp only [Prod.mk.injEq, true_and] at hww
        funext a c
        exact congrFun hww (a, c)
    rw [Fintype.card_piFinset] at h2
    have h3 : cst ^ r ≤ ∏ i' : Fin r, ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      have : cst ^ r = ∏ _i' : Fin r, cst := by simp
      rw [this]
      exact Finset.prod_le_prod₀ (fun _ _ => hcst0) fun i' _ => h1 i'
    refine le_trans h3 ?_
    exact_mod_cast h2
  have hA1 : A.card = ∑ τ : X.Tset p K j (X.restr j b), (A.filter fun x => x.1 = τ).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hA2 : A.card = ∑ e ∈ E, (A.filter fun x => φ x = e).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_coe.mpr (hφE x (Finset.mem_coe.mp hx))
  have hstep1 : (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r ≤ (A.card : ℝ) := by
    rw [hA1, Nat.card_eq_fintype_card]
    push_cast
    have : (Fintype.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r =
        ∑ _τ : X.Tset p K j (X.restr j b), cst ^ r := by
      simp
    rw [this]
    exact Finset.sum_le_sum fun τ _ => hcount τ
  refine le_trans hstep1 ?_
  rw [hA2]
  push_cast
  exact Finset.sum_le_sum fun e he => by exact_mod_cast hfib e he

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ) := by exact_mod_cast h4
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

end Formalism.MainNotions.SelectionLemmas.Pf
