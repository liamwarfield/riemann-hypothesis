module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultAt
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem val_digit {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (μ : σ → ℕ) :
    (∏ v, (ρ v + L v * μ v).factorial).factorization p =
      (∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v)).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, -⟩ := h2 σ t' ρ' hlt
  set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
  set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
  have hU0 : U ≠ 0 := (hunit e').1
  have hUv : padicValRat p U = 0 := (hunit e').2
  have key : ((∏ v, (ρ v + L v * μ v).factorial : ℕ) : ℚ) =
      ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) * U := by
    push_cast
    rw [hU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : odd v
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_pos hv] at this ⊢
      rw [(hodd v hv).1, this]
      ring
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_neg hv] at this ⊢
      rw [(hend v hv).1, (hend v hv).2]
      simp only [zero_add, mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, zero_add] at this ⊢
      rw [← this]
      simp
  have hQ0 : ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.2 fun v _ =>
      mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hv := congrArg (padicValRat p) key
  rw [padicValRat.mul hQ0 hU0, hUv, add_zero, padicValRat.of_nat, padicValRat.of_nat] at hv
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact_mod_cast hv

def tdeg (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (x : X.TT × Bool) : ℕ :=
  multideg (ioExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b)) x

def TrueDegAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∏ x : X.TT × Bool, (tdeg C0 CE1 CE2 X j b x).factorial = facSeg X j ∧
      ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) = lgSeg X j

def CoarseMultAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p ≤
        (expFact (mu0 C0 CE1 CE2 X j b)).factorization X.p + lgSeg X j

theorem kapNumAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hT : TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  obtain ⟨hT1, hT2⟩ := hT X hD1 hH hc j b hb
  have hM1 := hM X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b

  obtain ⟨M, hM0, hEM, hMv⟩ := expFact_mul X.p (tdeg C0 CE1 CE2 X j b) (ioExp C0 CE1 CE2 X j b μ0) (fun x => rfl)
  rw [hT1] at hEM
  have hMv' : M.factorization X.p ≤ X.m * lgSeg X j := by
    rw [← hT2, Finset.mul_sum]
    refine hMv.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    simp

  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  have hvd := val_digit h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) μ0
  have hE0 : expFact (ioExp C0 CE1 CE2 X j b μ0) ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hmu0 : expFact μ0 = ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
  have hR0 : Rblk C0 CE1 CE2 X j b ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP1 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
      symLev X.p C0 CE1 CE2 X j v * μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP2 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hP3 : (∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hsplit : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (μ0 v).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) =
      (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
        (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) * ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hvE : (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p =
      (PhiB C0 CE1 CE2 X j b).factorization X.p + (expFact μ0).factorization X.p := by
    rw [expFact_ioExp, Nat.factorization_mul hR0 hP1, Finsupp.add_apply, hvd, hsplit, Nat.factorization_mul hP2 hP3,
      Finsupp.add_apply, hmu0]
    unfold PhiB
    rw [Nat.factorization_mul hR0 hP2, Finsupp.add_apply]
    ring
  have hvF : (facSeg X j).factorization X.p = (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p +
      M.factorization X.p := by
    rw [← hEM, Nat.factorization_mul hE0 hM0, Finsupp.add_apply]

  have hdv : expFact μ0 ∣ ∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial := by
    have h := dvdAt C0 CE1 CE2 X j b hb μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b)
    unfold Nblk at h
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (specConst_ne _ _ _)) h
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hle : (expFact μ0).factorization X.p ≤ (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p :=
    (Nat.factorization_le_iff_dvd (by rw [hmu0]; exact hP3) hc0).2 hdv X.p
  constructor
  · rw [hvF, hvE]
    have : X.m * lgSeg X j ≤ (X.m + 1) * lgSeg X j := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  · rw [hvF, hvE]
    omega

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem ioBlock_wh' (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : ∀ (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' s
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL)) :
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
  have hS := hs ω' ωL ⟨h1, h2, h3⟩
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

theorem leading_exponent_weighted_homog (b : SegBlock (segS X.TT j) X.m) (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ)
    (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ) (hB : Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL) :
    IsWeightedHomogeneous ω' (monomial (mu0 C0 CE1 CE2 X j b) (1 : KK ℤ))
      (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL) := by
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω' i) (fun _ => zero_smul _ _)]
  simpa [smul_eq_mul] using leading_exponent_homogeneous C0 CE1 CE2 X j b ω' ωL hB

theorem tdeg_eq (b : SegBlock (segS X.TT j) X.m) (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (ho : b.oPlus ≤ segAPlus X.TT X.aT j) (x : X.TT × Bool) :
    tdeg C0 CE1 CE2 X j b x = (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have hwh := ioBlock_wh' C0 CE1 CE2 X j ℤ 0 b (wLet X x) (fun _ _ _ => rfl) (fun _ => rfl) rfl
    (monomial (mu0 C0 CE1 CE2 X j b) 1) (fun ω' ωL hB => leading_exponent_weighted_homog C0 CE1 CE2 X j b ω' ωL hB)
  rw [ioBlock_monomial] at hwh
  have h1 := hwh (by rw [coeff_monomial, if_pos rfl]; exact one_ne_zero)
  rw [weight_wLet] at h1
  unfold tdeg
  rw [h1, TD_wLet C0 CE1 CE2 X j x b hk ho]

theorem segPos_inj : Function.Injective (segPos X.TT j) := by
  intro i i' h
  exact topOdd_inj X j (Subtype.ext h)

@[to_additive]
theorem prod_tdeg {M : Type} [CommMonoid M] (g : ℕ → M) (hg : g 0 = 1) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    ∏ x : X.TT × Bool, g (tdeg C0 CE1 CE2 X j b x) =
      (∏ i : Fin (segS X.TT j), g (X.bT (segPos X.TT j i)) * g (X.aT (segPos X.TT j i))) *
        g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j)) := by
  classical
  set T : Fin X.n' → Bool → ℕ := fun t β => (if segNext X.TT j = t then hhDeg X.aT X.bT t β else 0) +
    ∑ i, (if segPos X.TT j i = t then hhDeg X.aT X.bT t β else 0) with hT
  have e : ∀ x : X.TT × Bool, tdeg C0 CE1 CE2 X j b x = T x.1.val x.2 := fun x => tdeg_eq C0 CE1 CE2 X j b hk ho x
  simp only [e]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [Finset.prod_coe_sort X.TT (fun t => g (T t true) * g (T t false))]
  have hnp : ∀ i, segPos X.TT j i ≠ segNext X.TT j := fun i h => (pos_mem X.TT j i).2 (h ▸ (next_mem X.TT j).2)
  have hS : insert (segNext X.TT j) (Finset.univ.image (segPos X.TT j)) ⊆ X.TT := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact (next_mem X.TT j).1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
      exact (pos_mem X.TT j i).1
  rw [← Finset.prod_subset hS (fun t _ ht => by
    have h1 : segNext X.TT j ≠ t := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have h2 : ∀ i, segPos X.TT j i ≠ t := fun i h => ht (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
    simp only [hT, if_neg h1, if_neg (h2 _), Finset.sum_const_zero, add_zero, hg, mul_one])]
  rw [Finset.prod_insert (fun h => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
    exact hnp i hi), Finset.prod_image (fun i _ i' _ h => segPos_inj X j h)]
  have hnext : ∀ β, T (segNext X.TT j) β = hhDeg X.aT X.bT (segNext X.TT j) β := by
    intro β
    show (if segNext X.TT j = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) +
      ∑ i, (if segPos X.TT j i = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) = _
    rw [if_pos rfl, Finset.sum_eq_zero (fun i _ => if_neg (hnp i)), add_zero]
  have hpos : ∀ i β, T (segPos X.TT j i) β = hhDeg X.aT X.bT (segPos X.TT j i) β := by
    intro i β
    show (if segNext X.TT j = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) +
      ∑ i', (if segPos X.TT j i' = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) = _
    rw [if_neg (fun h : segNext X.TT j = segPos X.TT j i => hnp i h.symm), zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (fun h => hi' (segPos_inj X j h))) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
  have hev := (next_mem X.TT j).2
  simp only [hnext, hpos, hhDeg, if_true, Bool.false_eq_true, if_false, if_pos hev]
  have hodd : ∀ i, ¬ Even (segPos X.TT j i).val := fun i => (pos_mem X.TT j i).2
  simp only [hodd, if_false]
  rw [mul_comm (g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j))), mul_assoc]

end

theorem trueDegAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD1 hH hc j b hb
  have ho := hO X hD1 hH hc j b hb
  constructor
  · rw [prod_tdeg C0 CE1 CE2 X j Nat.factorial rfl b hb ho]
    rfl
  · rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
    unfold lgSeg
    rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
