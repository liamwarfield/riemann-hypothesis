module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCount
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCount
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem score_tZero_level : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n,
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ)
      - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  intro n lev hm a
  have hlt : ∀ b, lev a < lev b → a < b := fun b h => by
    by_contra hc
    exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
  have h1 : ((tZero lev).filter fun p => p.1 = a).card
      = (univ.filter fun b => lev a < lev b).card := by
    symm
    refine Finset.card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    · intro b hb
      have hb' : lev a < lev b := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb', hlt b hb']
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨x, b⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨_, h⟩, rfl⟩ := hp
      exact ⟨b, by simp [h], rfl⟩
  have h2 : (((prs n) \ tZero lev).filter fun p => p.2 = a).card
      = (univ.filter fun b => b < a ∧ lev b = lev a).card := by
    symm
    refine Finset.card_bij (fun b _ => (b, a)) ?_ ?_ ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb'.1, hb'.2]
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).1
    · rintro ⟨b, x⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and,
        not_lt] at hp
      obtain ⟨⟨h, h'⟩, rfl⟩ := hp
      exact ⟨b, by simp [h, le_antisymm (hm h.le) (h' h)], rfl⟩
  have h3 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    simpa [Finset.filter_gt_eq_Iio] using Fin.card_Iio a
  have h4 : (univ.filter fun b => lev b < lev a).card
      + (univ.filter fun b => b < a ∧ lev b = lev a).card = (a : ℕ) := by
    rw [← h3, ← Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a)
      (fun b => lev b < lev a)]
    congr 2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, h⟩
        by_contra hc
        exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
      · exact fun h => h.2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, fun hc => absurd h' (ne_of_lt hc)⟩
      · rintro ⟨h, h'⟩
        exact ⟨h, le_antisymm (hm h.le) (not_lt.mp h')⟩
  unfold score
  rw [h1, h2]
  have h4' : ((univ.filter fun b => lev b < lev a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ lev b = lev a).card : ℤ) = ((a : ℕ) : ℤ) := by
    exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.CoefId
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCountStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.score_tZero_eq_level_count : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n, score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.score_tZero_level | exact GlobalTheory.CompanionTheory.CoefId.score_tZero_level | (intros; apply GlobalTheory.CompanionTheory.CoefId.score_tZero_level <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOne
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId.Unique

variable {n : ℕ}

theorem sum_mul_card_fiber (T : Finset (Fin n × Fin n)) (g : Fin n × Fin n → Fin n) (v : Fin n → ℤ) :
    ∑ a, v a * ((T.filter fun p => g p = a).card : ℤ) = ∑ p ∈ T, v (g p) := by
  have h : ∀ a, v a * ((T.filter fun p => g p = a).card : ℤ)
      = ∑ p ∈ T.filter (fun p => g p = a), v (g p) := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => v a) (fun p hp => by rw [(Finset.mem_filter.1 hp).2])]
    simp [mul_comm]
  simp_rw [h]
  exact Finset.sum_fiberwise T g (fun p => v (g p))

theorem pair_sum (v : Fin n → ℤ) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n) :
    ∑ a, v a * score T a = ∑ p ∈ prs n, (if p ∈ T then v p.1 else v p.2) := by
  have h1 : ∑ a, v a * score T a = ∑ p ∈ T, v p.1 + ∑ p ∈ prs n \ T, v p.2 := by
    simp only [score, mul_add, Finset.sum_add_distrib]
    rw [sum_mul_card_fiber T Prod.fst v, sum_mul_card_fiber (prs n \ T) Prod.snd v]
  have h2 : ∑ p ∈ prs n, (if p ∈ T then v p.1 else v p.2)
      = ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2)
        + ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2) := (Finset.sum_sdiff hT).symm
  have h3 : ∑ p ∈ prs n \ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ prs n \ T, v p.2 :=
    Finset.sum_congr rfl fun p hp => if_neg (Finset.mem_sdiff.1 hp).2
  have h4 : ∑ p ∈ T, (if p ∈ T then v p.1 else v p.2) = ∑ p ∈ T, v p.1 :=
    Finset.sum_congr rfl fun p hp => if_pos hp
  rw [h1, h2, h3, h4, add_comm]

theorem pair_le (v : Fin n → ℤ) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n) :
    ∑ a, v a * score T a ≤ ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  rw [pair_sum v T hT]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem tZero_subset (lev : Fin n → ℕ) : tZero lev ⊆ prs n := Finset.filter_subset _ _

theorem tZero_term (lev : Fin n → ℕ) (hlev : Monotone lev) (v : Fin n → ℤ)
    (h1 : ∀ a b, lev a < lev b → v b ≤ v a) (h2 : ∀ a b, a < b → lev a = lev b → v a ≤ v b)
    (p : Fin n × Fin n) (hp : p ∈ prs n) :
    (if p ∈ tZero lev then v p.1 else v p.2) = max (v p.1) (v p.2) := by
  have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  by_cases h : lev p.1 < lev p.2
  · have hm : p ∈ tZero lev := Finset.mem_filter.2 ⟨hp, h⟩
    rw [if_pos hm, max_eq_left (h1 _ _ h)]
  · have he : lev p.1 = lev p.2 := le_antisymm (hlev hlt.le) (not_lt.1 h)
    have hm : p ∉ tZero lev := fun hm => h (Finset.mem_filter.1 hm).2
    rw [if_neg hm, max_eq_right (h2 _ _ hlt he)]

theorem tZero_eq (lev : Fin n → ℕ) (hlev : Monotone lev) (v : Fin n → ℤ)
    (h1 : ∀ a b, lev a < lev b → v b ≤ v a) (h2 : ∀ a b, a < b → lev a = lev b → v a ≤ v b) :
    ∑ a, v a * score (tZero lev) a = ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  rw [pair_sum v _ (tZero_subset lev)]
  exact Finset.sum_congr rfl (tZero_term lev hlev v h1 h2)

theorem sum_sym (f : Fin n → Fin n → ℤ) (hf : ∀ a b, f a b = f b a) :
    ∑ a, ∑ b, f a b = 2 * ∑ p ∈ prs n, f p.1 p.2 + ∑ a, f a a := by
  have hsplit : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f b a else 0)
      + (if a = b then f a a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, h.le, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le, hf a b]
  have hA : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ p ∈ prs n, f p.1 p.2 := by
    rw [prs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hB : ∑ a, ∑ b, (if b < a then f b a else 0) = ∑ p ∈ prs n, f p.1 p.2 := by
    rw [Finset.sum_comm]; exact hA
  have hC : ∑ a, ∑ b, (if a = b then f a a else 0) = ∑ a, f a a := by simp
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if b < a then f b a else 0)
          + (if a = b then f a a else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = 2 * ∑ p ∈ prs n, f p.1 p.2 + ∑ a, f a a := by
        simp only [Finset.sum_add_distrib]
        rw [hA, hB, hC]; ring

theorem sum_max_perm (σ : Equiv.Perm (Fin n)) (v : Fin n → ℤ) :
    ∑ p ∈ prs n, max (v (σ p.1)) (v (σ p.2)) = ∑ p ∈ prs n, max (v p.1) (v p.2) := by
  have e1 := sum_sym (fun a b => max (v (σ a)) (v (σ b))) (fun a b => max_comm _ _)
  have e2 := sum_sym (fun a b => max (v a) (v b)) (fun a b => max_comm _ _)
  have e3 : ∑ a, ∑ b, max (v (σ a)) (v (σ b)) = ∑ a, ∑ b, max (v a) (v b) := by
    rw [← Equiv.sum_comp σ (fun a => ∑ b, max (v a) (v b))]
    exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => max (v (σ a)) (v b))
  have e4 : ∑ a, max (v (σ a)) (v (σ a)) = ∑ a, max (v a) (v a) :=
    Equiv.sum_comp σ (fun a => max (v a) (v a))
  linarith

theorem lev_symm_le {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ} (hL : StrictAnti L)
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) (a₀ : Fin n) :
    lev (σ.symm a₀) ≤ lev a₀ := by
  set j := lev a₀ with hj
  set w : Fin n → ℤ := fun a => if lev a ≤ j then 1 else 0 with hw
  have hw1 : ∀ a b, lev a < lev b → w b ≤ w a := by
    intro a b h
    simp only [hw]
    split_ifs <;> first | omega | simp
  have hw2 : ∀ a b, a < b → lev a = lev b → w a ≤ w b := by
    intro a b _ h
    simp only [hw, h]; exact le_refl _
  have hle : ∑ a, w a * score T a ≤ ∑ a, w a * score (tZero lev) a := by
    rw [tZero_eq lev hlev w hw1 hw2]; exact pair_le w T hT
  have hsum : ∑ a, w a * (L a - L (σ a)) ≤ 0 := by
    have : ∑ a, w a * score T a
        = ∑ a, w a * score (tZero lev) a + 2 * ∑ a, w a * (L a - L (σ a)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [hs a]; ring
    linarith

  set A : Finset (Fin n) := Finset.univ.filter fun a => lev a ≤ j with hA
  have hAne : A.Nonempty := ⟨a₀, by simp [hA, hj]⟩
  set b₀ := A.max' hAne with hb₀
  have hb₀A : lev b₀ ≤ j := by
    have := A.max'_mem hAne
    simpa [hA] using this
  set τ : ℤ := L b₀ - 1 with hτ
  have hin : ∀ a, lev a ≤ j → 1 ≤ L a - τ := by
    intro a ha
    have : a ≤ b₀ := A.le_max' a (by simp [hA, ha])
    have := hL.antitone this
    omega
  have hout : ∀ a, ¬ lev a ≤ j → L a - τ ≤ 0 := by
    intro a ha
    have hlt : b₀ < a := by
      by_contra hc
      exact ha ((hlev (not_lt.1 hc)).trans hb₀A)
    have := hL hlt
    omega
  set u : Fin n → ℤ := fun a => w (σ.symm a) with hu
  have hwσ : ∑ a, u a = ∑ a, w a := Equiv.sum_comp σ.symm w
  have huL : ∑ a, w a * L (σ a) = ∑ a, u a * L a := by
    rw [← Equiv.sum_comp σ (fun a => u a * L a)]
    simp [hu]
  have hid : ∑ a, (w a - u a) * (L a - τ) = ∑ a, w a * (L a - L (σ a)) := by
    have l : ∑ a, (w a - u a) * (L a - τ)
        = ∑ a, w a * L a - ∑ a, u a * L a - τ * (∑ a, w a - ∑ a, u a) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have m : ∑ a, w a * (L a - L (σ a)) = ∑ a, w a * L a - ∑ a, w a * L (σ a) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [l, m, huL, hwσ]; ring
  have hu01 : ∀ a, 0 ≤ u a ∧ u a ≤ 1 := by
    intro a
    simp only [hu, hw]
    split_ifs <;> simp
  have hnn : ∀ a, 0 ≤ (w a - u a) * (L a - τ) := by
    intro a
    by_cases ha : lev a ≤ j
    · have hwa : w a = 1 := by simp [hw, ha]
      rw [hwa]
      exact mul_nonneg (by linarith [(hu01 a).2]) (by linarith [hin a ha])
    · have hwa : w a = 0 := by simp [hw, ha]
      rw [hwa]
      nlinarith [(hu01 a).1, hout a ha]
  have hz : ∑ a, (w a - u a) * (L a - τ) = 0 :=
    le_antisymm (hid ▸ hsum) (Finset.sum_nonneg fun a _ => hnn a)
  have hz₀ := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hz a₀ (Finset.mem_univ _)
  by_contra hc
  have hu0 : u a₀ = 0 := by simp [hu, hw, hc]
  have hw0 : w a₀ = 1 := by simp [hw, hj]
  rw [hu0, hw0] at hz₀
  have := hin a₀ le_rfl
  simp only [sub_zero, one_mul] at hz₀
  omega

theorem lev_comp {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ} (hL : StrictAnti L)
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) (a : Fin n) :
    lev (σ a) = lev a := by
  have hle : ∀ a, lev (σ.symm a) ≤ lev a := lev_symm_le hlev hL σ T hT hs
  have hsum : ∑ a, lev (σ.symm a) = ∑ a, lev a := Equiv.sum_comp σ.symm lev
  have h := (Finset.sum_eq_sum_iff_of_le (fun a _ => hle a)).1 hsum (σ a) (Finset.mem_univ _)
  simpa using h.symm

def rk (lev : Fin n → ℕ) : Fin n → ℤ := fun a => -((n : ℤ) + 1) * (lev a : ℤ) + ((a : ℕ) : ℤ)

theorem rk_lt_of_lev {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    rk lev b < rk lev a := by
  simp only [rk]
  have ha : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
  have hb : ((b : ℕ) : ℤ) < n := by exact_mod_cast b.2
  have h' : (lev a : ℤ) + 1 ≤ lev b := by exact_mod_cast h
  have hn : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h' hn]

theorem rk_lt_of_eq {lev : Fin n → ℕ} {a b : Fin n} (hab : a < b) (h : lev a = lev b) :
    rk lev a < rk lev b := by
  simp only [rk, h]
  have : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  linarith

theorem sigma_eq_one {lev : Fin n → ℕ} (hlev : Monotone lev) {L : Fin n → ℤ}
    (h3 : ∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))
    (h4 : ∀ a b, lev a = lev b →
      score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ))
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (hs : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a)))
    (hl : ∀ a, lev (σ a) = lev a) : σ = 1 := by
  set t := score (tZero lev) with ht
  set r := rk lev with hr
  set d : Fin n → ℤ := fun a => ((σ a : ℕ) : ℤ) - ((a : ℕ) : ℤ) with hd
  have hr1 : ∀ a b, lev a < lev b → r b ≤ r a := fun a b h => (rk_lt_of_lev h).le
  have hr2 : ∀ a b, a < b → lev a = lev b → r a ≤ r b := fun a b h h' => (rk_lt_of_eq h h').le
  have hrd : ∀ a, r (σ a) = r a + d a := by
    intro a
    simp only [hr, rk, hd, hl a]
    ring
  have hLd : ∀ a, L a - L (σ a) = d a := fun a => h3 a (σ a) (hl a).symm
  have hCd : ∀ a, t (σ a) - r (σ a) = t a - r a := by
    intro a
    have := h4 (σ a) a (hl a)
    simp only [hr, rk, hl a]
    linarith
  have key : ∑ a, r (σ a) * score T a ≤ ∑ a, r a * t a := by
    calc ∑ a, r (σ a) * score T a ≤ ∑ p ∈ prs n, max (r (σ p.1)) (r (σ p.2)) :=
          pair_le (fun a => r (σ a)) T hT
      _ = ∑ p ∈ prs n, max (r p.1) (r p.2) := sum_max_perm σ r
      _ = ∑ a, r a * t a := (tZero_eq lev hlev r hr1 hr2).symm
  have e1 : ∑ a, r (σ a) * score T a
      = ∑ a, r a * t a + 3 * ∑ a, r a * d a + ∑ a, d a * (t a - r a) + 2 * ∑ a, d a ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs a, hLd a, hrd a]
    ring
  have e2 : ∑ a, d a * (t a - r a) = 0 := by
    have h := Equiv.sum_comp σ (fun a => r a * (t a - r a))
    have h' : ∑ a, r (σ a) * (t (σ a) - r (σ a))
        = ∑ a, r a * (t a - r a) + ∑ a, d a * (t a - r a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hCd a, hrd a]
      ring
    linarith
  have e3 : 2 * ∑ a, r a * d a + ∑ a, d a ^ 2 = 0 := by
    have h := Equiv.sum_comp σ (fun a => r a ^ 2)
    have h' : ∑ a, r (σ a) ^ 2 = ∑ a, r a ^ 2 + (2 * ∑ a, r a * d a + ∑ a, d a ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hrd a]
      ring
    linarith
  have hdd : ∑ a, d a ^ 2 = 0 := by
    refine le_antisymm (by linarith) (Finset.sum_nonneg fun a _ => by positivity)
  ext a
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hdd a
    (Finset.mem_univ _)
  have h1 : d a = 0 := by simpa using h0
  have h2 : ((σ a : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by
    simp only [hd] at h1
    linarith
  simpa using h2

theorem tournament_unique : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ L : Fin n → ℤ, StrictAnti L →
    (∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) →
    (∀ a b, lev a = lev b →
      score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ)) →
    ∀ (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)), T ⊆ prs n →
    (∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) → σ = 1 ∧ T = tZero lev := by
  intro n lev hlev L hL h3 h4 σ T hT hs
  have hσ : σ = 1 :=
    sigma_eq_one hlev h3 h4 σ T hT hs (lev_comp hlev hL σ T hT hs)
  refine ⟨hσ, ?_⟩
  subst hσ
  have hst : ∀ a, score T a = score (tZero lev) a := by
    intro a
    rw [hs a]
    simp
  have hr1 : ∀ a b, lev a < lev b → rk lev b ≤ rk lev a := fun a b h => (rk_lt_of_lev h).le
  have hr2 : ∀ a b, a < b → lev a = lev b → rk lev a ≤ rk lev b :=
    fun a b h h' => (rk_lt_of_eq h h').le
  have hsum : ∑ p ∈ prs n, (if p ∈ T then rk lev p.1 else rk lev p.2)
      = ∑ p ∈ prs n, max (rk lev p.1) (rk lev p.2) := by
    rw [← pair_sum (rk lev) T hT, ← tZero_eq lev hlev (rk lev) hr1 hr2]
    exact Finset.sum_congr rfl fun a _ => by rw [hst a]
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun p _ => by
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _)).1 hsum
  ext p
  constructor
  · intro hp
    have hpp := hT hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.1 hpp).2
    have h := hterm p hpp
    rw [if_pos hp] at h
    refine Finset.mem_filter.2 ⟨hpp, ?_⟩
    by_contra hc
    have he : lev p.1 = lev p.2 := le_antisymm (hlev hlt.le) (not_lt.1 hc)
    have h1 := rk_lt_of_eq hlt he
    have h2 := le_max_right (rk lev p.1) (rk lev p.2)
    omega
  · intro hp
    obtain ⟨hpp, hlt⟩ := Finset.mem_filter.1 hp
    by_contra hc
    have h := hterm p hpp
    rw [if_neg hc] at h
    have h1 := rk_lt_of_lev hlt
    have h2 := le_max_left (rk lev p.1) (rk lev p.2)
    omega

end GlobalTheory.CompanionTheory.CoefId.Unique
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOneStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.score_rigidity_perm_eq_one : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ L : Fin n → ℤ, StrictAnti L → (∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) → (∀ a b, lev a = lev b → score (tZero lev) a - ((a : ℕ) : ℤ) = score (tZero lev) b - ((b : ℕ) : ℤ)) → ∀ (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n × Fin n)), T ⊆ prs n → (∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) → σ = 1 ∧ T = tZero lev := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | exact GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique | (intros; apply GlobalTheory.CompanionTheory.CoefId.Unique.tournament_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScore
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScore
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_pairs_add_eq_sum_score {n : ℕ} (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  have h1 : ∀ (S : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n),
      ∏ p ∈ S, z (f p) = ∏ a, z a ^ (S.filter fun p => f p = a).card := by
    intro S f
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), prod_const]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [h1 T Prod.fst, h1 (prs n \ T) Prod.snd, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  have : score T a = (((T.filter fun p => p.1 = a).card + ((prs n \ T).filter fun p => p.2 = a).card : ℕ) : ℤ) := by
    simp [score]
  rw [this, zpow_natCast, pow_add]

end GlobalTheory.CompanionTheory.CoefId
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScoreStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score : ∀ {n : ℕ} (z : Fin n → ℂ), ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | exact GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProduct
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_prod_symm_eq_diag_mul_prs_sq {n : ℕ} (g : Fin n → Fin n → ℂ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b, g a b = (∏ a, g a a) * (∏ p ∈ prs n, g p.1 p.2) ^ 2 := by
  have h1 : ∏ a, ∏ b, g a b = ∏ p : Fin n × Fin n, g p.1 p.2 :=
    (Fintype.prod_prod_type' (f := g)).symm
  have hd : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => p.1 = p.2),
      g p.1 p.2 = ∏ a, g a a := by
    refine Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro a _; simp
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      ext <;> simp [this]
    · intro a _; rfl
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      simp [← this]
  have ho : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => ¬ p.1 = p.2),
      g p.1 p.2 = ∏ p ∈ prs n, g p.1 p.2 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [prs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hp.1) (Ne.symm hp.2)
    · intro p hp
      have hlt : p.1 < p.2 := by simpa [prs] using hp
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨not_lt.mpr hlt.le, hlt.ne'⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simpa using hg p.1 p.2
  rw [h1, ← Finset.prod_filter_mul_prod_filter_not univ (fun p : Fin n × Fin n => p.1 < p.2),
    ← Finset.prod_filter_mul_prod_filter_not (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2)
      (fun p => p.1 = p.2), hd, ho]
  change (∏ p ∈ prs n, g p.1 p.2) * _ = _
  ring

theorem prod_one_add_div_mul_prod_pow {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1)
      = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  have hZ : (∏ a, z a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hz a
  have h1 : ∏ a, ∏ b, (1 + z a / z b) = (∏ a, ∏ b, (z a + z b)) / (∏ a, z a) ^ n := by
    have hterm : ∀ a b, 1 + z a / z b = (z a + z b) / z b := by
      intro a b
      field_simp [hz b]
      ring
    simp only [hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : ∏ a, ∏ b, (z a + z b) = 2 ^ n * (∏ a, z a) * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
    rw [prod_prod_symm_eq_diag_mul_prs_sq (fun a b => z a + z b) (fun a b => add_comm _ _)]
    have : ∏ a, (z a + z a) = 2 ^ n * ∏ a, z a := by
      simp only [← two_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
  have h3 : (∏ a, z a) * (∏ a, z a) ^ (n - 1) = (∏ a, z a) ^ n := by
    rcases n with _ | m
    · simp
    · simp [pow_succ, mul_comm]
  rw [h1, h2]
  field_simp
  rw [mul_comm (∏ a, z a), ← h3]
  ring

end GlobalTheory.CompanionTheory.CoefId
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProductStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

lemma prod_prs_eq_iter {n : ℕ} (f : Fin n × Fin n → ℂ) :
    ∏ p ∈ prs n, f p = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  apply Finset.prod_finset_product
  intro p
  simp [prs]

lemma det_rev_vandermonde {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) *
        ∏ p ∈ prs n, (v p.2 - v p.1) := by
  have h : (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i j
    have : n - 1 - (j : ℕ) = n - (j + 1) := by omega
    simp [Matrix.vandermonde_apply, Fin.val_rev, this]
  rw [h, Matrix.det_permute', Matrix.det_vandermonde, prod_prs_eq_iter]

theorem det_vandermonde_sq {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det *
        ∏ p ∈ prs n, (z p.1 + z p.2) := by
  rw [det_rev_vandermonde (fun i => z i ^ 2), det_rev_vandermonde z, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

end GlobalTheory.CompanionTheory.CoefId
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquaresStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_squares : ∀ {n : ℕ} (z : Fin n → ℂ), (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det = (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | exact GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | (intros; apply GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficient
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.CoefId
variable {n : ℕ}

theorem coeff_eq {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ)
    (e' : κ → Fin n → ℤ)
    (h : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) (m : Fin n → ℤ) :
    ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j :=
  GlobalTheory.T.monomial_coefficient_comparison I J f g e e' h m

theorem flip_prod (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 :=
  GlobalTheory.T.weyl_denominator_product z h0

theorem den_sq (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) :=
  GlobalTheory.T.vandermonde_squares z

theorem den_ne_zero (t : Fin n → ℂ) (ht : Function.Injective t) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde t).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [h, Matrix.det_permute']
  exact mul_ne_zero (by simp) (Matrix.det_vandermonde_ne_zero_iff.2 ht)

theorem prod_expand (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, mon (score T) z :=
  GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score z

theorem alt_expand (e : Fin n → ℤ) (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => z i ^ e j).det =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * mon (fun a => e (σ a)) z := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem score_tZero (lev : Fin n → ℕ) (hm : Monotone lev) (a : Fin n) :
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ) -
      ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) :=
  GlobalTheory.T.score_tZero_eq_level_count lev hm a

theorem step_unique (lev : Fin n → ℕ) (hm : Monotone lev) (L : Fin n → ℤ) (hL : StrictAnti L)
    (hb : ∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (h : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) : σ = 1 ∧ T = tZero lev :=
  GlobalTheory.T.score_rigidity_perm_eq_one lev hm L hL hb (fun a b hab => by
    rw [score_tZero lev hm a, score_tZero lev hm b]
    simp only [hab, add_sub_cancel_right]) σ T hT h

theorem perm_unique (x y : Fin n → ℤ) (hx : StrictAnti x) (hy : StrictAnti y) (σ : Equiv.Perm (Fin n))
    (h : ∀ a, x (σ a) = y a) : σ = 1 := by
  have hs : StrictMono σ := fun a b hab => by
    have h1 := hy hab
    rw [← h a, ← h b] at h1
    rcases lt_trichotomy (σ a) (σ b) with h2 | h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (lt_irrefl _)
    · exact absurd (hx h2) (not_lt.2 h1.le)
  have h3 : hs.orderIsoOfSurjective σ σ.surjective = OrderIso.refl _ := Subsingleton.elim _ _
  exact Equiv.ext fun a => DFunLike.congr_fun h3 a

theorem harmZ_spec (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hlev : IsLev lam lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 : lev a ≤ lev b := hlev.1 hab
  have h2 := hl hab
  have h3 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have h4 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

end GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId
variable {n : ℕ}

theorem mon_shift (x y : Fin n → ℤ) (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0) :
    mon (fun a => x a + y a - ((n : ℤ) - 1)) z = mon x z * mon y z * ((∏ a, z a) ^ (n - 1))⁻¹ := by
  have hc : ∏ a, z a ^ (-((n : ℤ) - 1)) = ((∏ a, z a) ^ (n - 1))⁻¹ := by
    cases n with
    | zero => simp
    | succ m =>
      have : (-(((m + 1 : ℕ) : ℤ) - 1)) = -(m : ℤ) := by push_cast; ring
      rw [this]
      simp only [_root_.zpow_neg, zpow_natCast, Nat.add_sub_cancel]
      rw [Finset.prod_inv_distrib, Finset.prod_pow]
  unfold mon
  rw [← hc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  show z a ^ (x a + y a - ((n : ℤ) - 1)) = _
  rw [sub_eq_add_neg (x a + y a), zpow_add₀ (h0 a), zpow_add₀ (h0 a)]

theorem torus_id (lam : Fin n → ℤ) (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) *
        (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det =
      2 ^ n * ∑ σ : Equiv.Perm (Fin n), ∑ T ∈ (prs n).powerset, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a)) + score T a - ((n : ℤ) - 1)) z := by
  have hD : (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det ≠ 0 :=
    den_ne_zero (fun a => z a ^ 2) hinj
  have hDe := den_sq z
  rw [hDe] at hD
  set A := (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det with hA
  set P := ∏ p ∈ prs n, (z p.1 + z p.2) with hP
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hD
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hD
  have hZ0 : (∏ a, z a) ^ (n - 1) ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun a _ => h0 a)
  have hN : (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a))) z := by
    rw [← alt_expand (fun j => 2 * (lam j + dl n j)) z]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, dl]
    rw [← zpow_natCast, ← _root_.zpow_mul]
    norm_num
  have hF := flip_prod z h0
  have hR : ∑ σ : Equiv.Perm (Fin n), ∑ T ∈ (prs n).powerset, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a)) + score T a - ((n : ℤ) - 1)) z =
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a))) z) * P * ((∏ a, z a) ^ (n - 1))⁻¹ := by
    rw [hP, prod_expand, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mon_shift (fun a => 2 * (lam (σ a) + dl n (σ a))) (score T) z h0]
    simp only [mon]
    ring
  rw [hR, ← hN]
  have hW : weylChar lam (fun a => z a ^ 2) =
      (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det / (A * P) := by
    rw [← hDe]; rfl
  rw [hW]
  field_simp
  linear_combination (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det * hF

theorem exp_tZero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (a : Fin n) :
    2 * (lam a + dl n a) + score (tZero lev) a - ((n : ℤ) - 1) = muZ lam lev a + dl n a := by
  have h1 : dl n a = (n : ℤ) - 1 - (a : ℕ) := by
    have := a.2
    simp only [dl]
    omega
  rw [score_tZero lev hm, muZ, h1]
  ring

theorem dl_strictAnti : StrictAnti (dl n) := by
  intro a b h
  have h1 := a.2
  have h2 := b.2
  have h3 : (a : ℕ) < b := h
  simp only [dl]
  omega

theorem main_coef {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (F : Finset (Fin n → ℤ)) (hF : ∀ ν ∈ F, Antitone ν)
    (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2))
    (μ : Fin n → ℤ) (hμ : μ ∈ harmZ lam) : μ ∈ F ∧ c μ = 2 ^ n := by
  classical
  obtain ⟨lv, hlv, rfl⟩ := Finset.mem_image.1 hμ
  set lev : Fin n → ℕ := fun a => (lv a : ℕ) with hlevdef
  have hlev : IsLev lam lev := (Finset.mem_filter.1 hlv).2
  have hm : Monotone lev := hlev.1
  set μ := muZ lam lev with hμdef
  have hμa : Antitone μ := harmZ_spec lam hl lev hlev
  have key := coeff_eq (F ×ˢ (univ : Finset (Equiv.Perm (Fin n))))
    ((univ : Finset (Equiv.Perm (Fin n))) ×ˢ (prs n).powerset)
    (fun x => c x.1 * ((Equiv.Perm.sign x.2 : ℤ) : ℂ)) (fun x => 2 ^ n * ((Equiv.Perm.sign x.1 : ℤ) : ℂ))
    (fun x a => x.1 (x.2 a) + dl n (x.2 a))
    (fun x a => 2 * (lam (x.1 a) + dl n (x.1 a)) + score x.2 a - ((n : ℤ) - 1))
    (by
      intro z hz hinj
      have h0 : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
      have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
      have hA := den_ne_zero z hzi
      have ht := torus_id lam z h0 hinj
      have hnum : ∀ ν : Fin n → ℤ, weylChar ν z * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det =
          ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * mon (fun a => ν (σ a) + dl n (σ a)) z := by
        intro ν
        rw [weylChar, div_mul_cancel₀ _ hA]
        exact alt_expand (fun j => ν j + dl n j) z
      rw [← hc z hz hinj] at ht
      rw [Finset.sum_product, Finset.sum_product]
      have e1 : ∑ x ∈ F, ∑ y : Equiv.Perm (Fin n), c x * ((Equiv.Perm.sign y : ℤ) : ℂ) *
          mon (fun a => x (y a) + dl n (y a)) z =
          (∑ ν ∈ F, c ν * weylChar ν z) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [mul_assoc, hnum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
      refine e1.trans (ht.trans ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T _ => by ring)
    (fun a => μ a + dl n a)
  have hLs : StrictAnti (fun a => lam a + dl n a) := fun a b h =>
    add_lt_add_of_le_of_lt (hl h.le) (dl_strictAnti h)
  have hRf : ((univ : Finset (Equiv.Perm (Fin n))) ×ˢ (prs n).powerset).filter
      (fun x => (fun a => 2 * (lam (x.1 a) + dl n (x.1 a)) + score x.2 a - ((n : ℤ) - 1)) = fun a => μ a + dl n a) =
      {(1, tZero lev)} := by
    ext ⟨σ, T⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powerset,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hT, he⟩
      refine step_unique lev hm (fun a => lam a + dl n a) hLs (fun a b hab => ?_) σ T hT fun a => ?_
      · have h1 := a.2
        have h2 := b.2
        simp only [hlev.2 a b hab, dl]
        omega
      · have h1 := congrFun he a
        have h2 := exp_tZero lam lev hm a
        linarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨Finset.filter_subset _ _, funext fun a => by simpa using exp_tZero lam lev hm a⟩
  have hLf : (F ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).filter
      (fun x => (fun a => x.1 (x.2 a) + dl n (x.2 a)) = fun a => μ a + dl n a) =
      if μ ∈ F then {(μ, 1)} else ∅ := by
    ext ⟨ν, σ⟩
    have hu : (ν, σ) ∈ (F ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).filter
        (fun x => (fun a => x.1 (x.2 a) + dl n (x.2 a)) = fun a => μ a + dl n a) ↔ μ ∈ F ∧ ν = μ ∧ σ = 1 := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hν, he⟩
        have hs : σ = 1 := perm_unique (fun a => ν a + dl n a) (fun a => μ a + dl n a)
          (fun a b h => add_lt_add_of_le_of_lt (hF ν hν h.le) (dl_strictAnti h))
          (fun a b h => add_lt_add_of_le_of_lt (hμa h.le) (dl_strictAnti h)) σ (fun a => congrFun he a)
        subst hs
        have hν' : ν = μ := funext fun a => by simpa using congrFun he a
        subst hν'
        exact ⟨hν, rfl, rfl⟩
      · rintro ⟨hμF, rfl, rfl⟩
        exact ⟨hμF, rfl⟩
    rw [hu]
    split_ifs with h <;> simp [h]
  rw [hLf, hRf] at key
  by_cases hmem : μ ∈ F
  · rw [if_pos hmem, Finset.sum_singleton, Finset.sum_singleton] at key
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, mul_one] at key
    exact ⟨hmem, key⟩
  · rw [if_neg hmem, Finset.sum_empty, Finset.sum_singleton] at key
    exact absurd key.symm (by simpa using pow_ne_zero n (two_ne_zero (α := ℂ)))

end GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem coef_harm : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (F : Finset (Fin n → ℤ)), (∀ ν ∈ F, Antitone ν) →
    ∀ c : (Fin n → ℤ) → ℂ, (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2)) →
    ∀ μ ∈ harmZ lam, μ ∈ F ∧ c μ = 2 ^ n :=
  fun lam hl F hF c hc μ hμ => main_coef lam hl F hF c hc μ hμ

end GlobalTheory.CompanionTheory.CoefId
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficientStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_weights_coefficient : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (F : Finset (Fin n → ℤ)), (∀ ν ∈ F, Antitone ν) → ∀ c : (Fin n → ℤ) → ℂ, (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2)) → ∀ μ ∈ harmZ lam, μ ∈ F ∧ c μ = 2 ^ n := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.coef_harm | exact GlobalTheory.CompanionTheory.CoefId.coef_harm | (intros; apply GlobalTheory.CompanionTheory.CoefId.coef_harm <;> assumption)
end
