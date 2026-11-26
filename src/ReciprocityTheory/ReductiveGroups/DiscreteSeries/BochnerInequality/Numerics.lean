module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NumRho
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section NumRho

variable {ε : Fin n → Bool}

theorem numRho_dot_root_left (a b : Fin n) (v : Fin n → ℝ) : dot (root a b) v = v a - v b := by
  simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

theorem numRho_dot_root_right (a b : Fin n) (v : Fin n → ℝ) : dot v (root a b) = v a - v b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem numRho_cardR (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) = ∑ c, if p c then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]

private theorem rhoC_bound (ε : Fin n → Bool) (a : Fin n) :
    |2 * rhoC ε a| + 1 ≤ ((univ.filter fun c => ε c = ε a).card : ℝ) := by
  have h2 : 2 * rhoC ε a = ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := by
    simp only [rhoC]
    ring
  have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  have key : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => ε c = ε a).card : ℝ) := by
    have h1 : ∑ c : Fin n, (if c = a then (1:ℝ) else 0) = 1 := by simp
    rw [← h1]
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    rcases lt_trichotomy c a with h | h | h
    · simp [h, not_lt.mpr h.le, h.ne]
    · subst h
      simp
    · simp [h, not_lt.mpr h.le, h.ne']
  rw [h2]
  have habs : |((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ)| ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) +
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem abs_dot_root_rhoC_le {a b : Fin n} (hε : ε a ≠ ε b) :
    |dot (root a b) (rhoC ε)| ≤ ((n : ℝ) - 2) / 2 := by
  rw [numRho_dot_root_left]
  have ha := rhoC_bound ε a
  have hb := rhoC_bound ε b
  have hsum : ((univ.filter fun c => ε c = ε a).card : ℝ) +
      ((univ.filter fun c => ε c = ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c = ε a then (1:ℝ) else 0) + if ε c = ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  rw [abs_le]
  constructor <;> linarith [le_abs_self (2 * rhoC ε a), neg_abs_le (2 * rhoC ε a),
    le_abs_self (2 * rhoC ε b), neg_abs_le (2 * rhoC ε b)]

private theorem card_opposite_sign_above_add_below_eq (ε : Fin n → Bool) (x : Fin n) :
    ((univ.filter fun c => x < c ∧ ε c ≠ ε x).card : ℝ) +
      ((univ.filter fun c => c < x ∧ ε c ≠ ε x).card : ℝ) =
      ((univ.filter fun c => ε c ≠ ε x).card : ℝ) := by
  simp only [numRho_cardR]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rcases lt_trichotomy c x with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    simp
  · simp [h, not_lt.mpr h.le]

theorem dot_rhoN_root_ge {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 - (n : ℝ) / 2 ≤ dot (rhoN ε) (root a b) := by
  rw [numRho_dot_root_right]
  have hA := card_opposite_sign_above_add_below_eq ε a
  have hB := card_opposite_sign_above_add_below_eq ε b
  have hsum : ((univ.filter fun c => ε c ≠ ε a).card : ℝ) +
      ((univ.filter fun c => ε c ≠ ε b).card : ℝ) = n := by
    simp only [numRho_cardR]
    rw [← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n,
        ((if ε c ≠ ε a then (1:ℝ) else 0) + if ε c ≠ ε b then (1:ℝ) else 0) = 1 := by
      intro c
      cases h1 : ε c <;> cases h2 : ε a <;> cases h3 : ε b <;> simp_all
    simp only [hc]
    simp
  have hUa : (1:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := by
    have h : 0 < (univ.filter fun c => a < c ∧ ε c ≠ ε a).card :=
      Finset.card_pos.mpr ⟨b, by simp [hab, Ne.symm hε]⟩
    exact_mod_cast h
  have hLb : (1:ℝ) ≤ ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    have h : 0 < (univ.filter fun c => c < b ∧ ε c ≠ ε b).card :=
      Finset.card_pos.mpr ⟨a, by simp [hab, hε]⟩
    exact_mod_cast h
  have hra : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
      ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
    simp only [rhoN]
    ring
  have hrb : 2 * rhoN ε b = ((univ.filter fun c => b < c ∧ ε c ≠ ε b).card : ℝ) -
      ((univ.filter fun c => c < b ∧ ε c ≠ ε b).card : ℝ) := by
    simp only [rhoN]
    ring
  linarith

theorem numRho_sum_opp (ε : Fin n → Bool) :
    (∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) = 2 * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have h1 : ∀ a : Fin n, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
      if ε a = true then (qOf ε : ℝ) else (pOf ε : ℝ) := by
    intro a
    cases h : ε a <;> simp [pOf, qOf]
  have hq : (univ.filter fun x => ¬ ε x = true).card = qOf ε := by simp [qOf]
  have hp : (univ.filter fun x => ε x = true).card = pOf ε := rfl
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    hq, hp]
  simp only [nsmul_eq_mul]
  ring

theorem two_dot_rhoC_rhoN_le (ε : Fin n → Bool) :
    2 * dot (rhoC ε) (rhoN ε) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have key : ∀ a : Fin n, 2 * (rhoC ε a * rhoN ε a) ≤
      (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
    intro a
    have hb := rhoC_bound ε a
    have hcn : ((univ.filter fun c => ε c = ε a).card : ℝ) ≤ n := by
      have h := Finset.card_filter_le (univ : Finset (Fin n)) (fun c => ε c = ε a)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact_mod_cast h
    have hs := card_opposite_sign_above_add_below_eq ε a
    have hr : 2 * rhoN ε a = ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) -
        ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := by
      simp only [rhoN]
      ring
    have hU : (0:ℝ) ≤ ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hL : (0:ℝ) ≤ ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ) := Nat.cast_nonneg _
    have hC : |2 * rhoC ε a| ≤ (n : ℝ) := by linarith
    have hN : |2 * rhoN ε a| ≤ ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
      rw [hr]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have he : (2 * rhoC ε a) * (2 * rhoN ε a) ≤ |2 * rhoC ε a| * |2 * rhoN ε a| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hm : |2 * rhoC ε a| * |2 * rhoN ε a| ≤
        (n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
      mul_le_mul hC hN (abs_nonneg _) (Nat.cast_nonneg n)
    have h4 : (2 * rhoC ε a) * (2 * rhoN ε a) = 4 * (rhoC ε a * rhoN ε a) := by ring
    have h5 : (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
        ((n : ℝ) * ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) / 2 := by ring
    linarith
  rw [dot, Finset.mul_sum]
  calc ∑ a, 2 * (rhoC ε a * rhoN ε a)
      ≤ ∑ a, (n : ℝ) / 2 * ((univ.filter fun c => ε c ≠ ε a).card : ℝ) :=
        Finset.sum_le_sum (fun a _ => key a)
    _ = (n : ℝ) / 2 * ∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
        rw [numRho_sum_opp]
        ring

theorem nsq_root {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  rw [nsq, numRho_dot_root_left]
  simp [root, Pi.single_apply, hab, Ne.symm hab] <;> norm_num

private theorem nsq_add_bochner_inequality (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem casValK_add (μ ν : Fin n → ℝ) :
    casValK ε (μ + ν) = casValK ε μ + 2 * dot (μ + rhoC ε) ν + nsq ν := by
  simp only [casValK]
  rw [add_right_comm μ ν (rhoC ε), nsq_add_bochner_inequality]
  ring

theorem lowK_add_rhoC (lam : Fin n → ℝ) : lowK ε lam + rhoC ε = lam + rhoN ε := by
  simp only [lowK, sub_add_cancel]

end NumRho

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]

private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]

private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]

private theorem dot_neg_r (u v : Fin n → ℝ) : dot u (-v) = - dot u v := by
  simp only [dot, Pi.neg_apply, mul_neg, sum_neg_distrib]

private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, mul_sum]
  exact Finset.sum_comm

private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, Pi.single_apply, mul_sub, sum_sub_distrib]

private theorem root_swap (a b : Fin n) : root b a = - root a b := by
  simp [root]

private theorem nsq_nonneg'' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)

private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot_add_l, dot_add_r, dot_comm' v u]; ring

private theorem dot_le_sqrt (u v : Fin n → ℝ) : dot u v ≤ √(nsq u) * √(nsq v) := by
  rw [← Real.sqrt_mul (nsq_nonneg'' u)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  simpa [dot, nsq, sq] using Finset.sum_mul_sq_le_sq_mul_sq univ u v

private theorem sqrt_nsq_add_le (u v : Fin n → ℝ) : √(nsq (u + v)) ≤ √(nsq u) + √(nsq v) := by
  have h1 : nsq (u + v) ≤ (√(nsq u) + √(nsq v)) ^ 2 := by
    rw [nsq_add'', add_sq, Real.sq_sqrt (nsq_nonneg'' u), Real.sq_sqrt (nsq_nonneg'' v)]
    nlinarith [dot_le_sqrt u v]
  calc √(nsq (u + v)) ≤ √((√(nsq u) + √(nsq v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

private theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nsq, dot]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (by linarith)

private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have hsum : pOf ε + qOf ε = n := by
    unfold pOf qOf
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this
  have hp : ∃ c, ε c = true := by
    cases ha : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, ha⟩
  have hq : ∃ c, ε c = false := by
    cases ha : ε a
    · exact ⟨a, ha⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  have h1 : 1 ≤ pOf ε := Finset.card_pos.mpr ⟨c, by simp [hc]⟩
  have h2 : 1 ≤ qOf ε := Finset.card_pos.mpr ⟨d, by simp [hd]⟩
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩

theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨hp, hq, hn⟩ := pq_facts hε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)
  have key : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
    nlinarith [mul_nonneg hn0 hm]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem sch_gap {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by
  obtain ⟨hanti, h, hg, hbig⟩ := hgap
  have h1 := hg a b hε
  have hlt : lam b < lam a := hanti hab
  rw [abs_of_pos (sub_pos.2 hlt)] at h1
  rw [dot_root_r]
  linarith [two_dot_rhoC_rhoN_le ε]

theorem crossVal_pos {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_lt hab), dot_add_l, dot_root_r lam]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem crossVal_neg {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    casValK ε (lowK ε lam + root b a) - n - casValK ε (lowK ε lam) ≤ -2 * h - 2 := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_gt hab), dot_add_l, dot_root_r lam,
    root_swap a b, dot_neg_r]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem isNCSum_zero {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by
  constructor
  · rintro ⟨γ, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem isNCSum_succ_exists {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by
  obtain ⟨γ, hγ, -⟩ := hν
  exact ⟨_, _, hγ 0⟩

theorem vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  obtain ⟨hg1, hg2⟩ := gap_gt (hγ ⟨0, hj⟩) hbig
  have hρ : -((j : ℝ) * (((n : ℝ) - 2) / 2)) ≤ dot (rhoC ε) (∑ i, root (γ i).1 (γ i).2) := by
    rw [dot_sum_r]
    have : ∑ _i : Fin j, -(((n : ℝ) - 2) / 2) ≤ ∑ i, dot (rhoC ε) (root (γ i).1 (γ i).2) := by
      apply Finset.sum_le_sum
      intro i _
      have := abs_dot_root_rhoC_le (ε := ε) (hγ i)
      rw [dot_comm'] at this
      linarith [neg_abs_le (dot (rhoC ε) (root (γ i).1 (γ i).2))]
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] using this
  rw [casValK_add] at hc
  have e2 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e3 : Λ + (∑ i, root (γ i).1 (γ i).2) + (2 : ℝ) • rhoC ε =
      ((Λ + rhoC ε) + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by rw [two_smul]; abel
  rw [e2, e3, nsq_add'' ((Λ + rhoC ε) + rhoC ε), dot_add_l]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos : 0 ≤ 2 * h - 3 * (n : ℝ) + 4 := by linarith
  nlinarith [mul_nonneg hj0 hpos]

theorem degree_num {Λ ν : Fin n → ℝ} {j k : ℕ} (hjk : j ≤ k) (hν : IsNCSum ε j ν) :
    casValK ε (Λ + ν) ≤ (√(nsq (Λ + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  have hs : √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √2 * k := by
    refine (sqrt_nsq_sum_le _ _).trans ?_
    have : ∀ i, √(nsq (root (γ i).1 (γ i).2)) = √2 := fun i => by
      rw [nsq_root (fun e => hγ i (by rw [e]))]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Real.sqrt_nonneg 2)
  unfold casValK
  have e : Λ + (∑ i, root (γ i).1 (γ i).2) + rhoC ε = (Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by
    abel
  rw [e]
  have h1 := (sqrt_nsq_add_le (Λ + rhoC ε) (∑ i, root (γ i).1 (γ i).2)).trans (by linarith [hs] :
    √(nsq (Λ + rhoC ε)) + √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √(nsq (Λ + rhoC ε)) + √2 * k)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (nsq_nonneg'' _)] at h2
  linarith

end Num

end ReciprocityTheory.ChartRestriction.DS
