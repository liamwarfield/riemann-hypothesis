module

public import Development.AutomorphicArithmetic.ThickFrames.orbitTerms
public import Development.AutomorphicArithmetic.ThickFrames.MarkedGe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThickFrames.NotGoodLe
section -- merged from Development.AutomorphicArithmetic.ThickFrames.TilesLe
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open GlobalTheory.RandomTops (tile tile_disjoint marked_congr)

private theorem ind_neg' {q : Prop} (h : ¬ q) : ind q = 0 := by simp [ind, h]

private theorem ind_le_one' (q : Prop) : ind q ≤ 1 := by
  by_cases h : q <;> simp [ind, h]

private theorem ind_le' {q : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : q → 1 ≤ x) : ind q ≤ x := by
  by_cases h : q
  · simpa [ind, h] using h1 h
  · simpa [ind, h] using h0

private theorem bernoulliExpectation_one_sub (p : ℕ → ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    exP p S (fun T => 1 - f T) = 1 - exP p S f := by
  have := (expectation_spec p).2.1 S (fun T => 1 - f T) f
  simp only [sub_add_cancel] at this
  rw [(expectation_spec p).1] at this
  linarith

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tiles_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n r u M₀ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤ n * (1 - markedLow δ r u) ^ M₀ := by
  intro p δ n r u M₀ i₀ hp h0 h1 hu hn
  obtain ⟨ex_const, -, ex_sum, ex_mono', -, -, ex_prod⟩ := expectation_spec p
  have ex_mono : ∀ {S : Finset ℕ} {f g : Finset ℕ → ℝ}, (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g :=
    fun {S f g} h => ex_mono' S f g (fun a _ => ⟨by linarith [(hp a).1], (hp a).2.trans h1⟩) h
  have hmk : ∀ s, markedLow δ r u ≤ exP p (tile r u s) (fun T => ind (Marked T r u s)) :=
    fun s => marked_ge p δ r u s hp h0 h1
  have h1' : 0 ≤ 1 - δ := by linarith
  have hl : 0 < (6 * r + 1) * u := by positivity
  set l := (6 * r + 1) * u with hldef
  set t := n / l with ht
  have hMt : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hl).2 hn
  have hP1 : ∀ s, exP p (tile r u s) (fun T => ind (Marked T r u s)) ≤ 1 := fun s =>
    (ex_mono fun T _ => ind_le_one' _).trans (ex_const _ _).le
  have hπ0 : 0 ≤ markedLow δ r u := by unfold markedLow; positivity
  have hπ1 : markedLow δ r u ≤ 1 := (hmk 0).trans (hP1 0)
  let J : ℕ → Finset ℕ := fun s₀ =>
    ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).erase (i₀ / l)
  have hJc : ∀ s₀, M₀ ≤ (J s₀).card := fun s₀ => by
    have h2 : ((Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t).card = M₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
      have hj' := Finset.mem_range.1 (Finset.mem_coe.1 hj)
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' s₀ hij) (by omega) (by omega)
    have h3 := Finset.pred_card_le_card_erase
      (s := (Finset.range (M₀ + 1)).image fun j => (s₀ + j) % t) (a := i₀ / l)
    simp only [J]
    omega
  have hnot : ∀ s, s ≠ i₀ / l → i₀ ∉ tile r u s := fun s hs h => by
    rw [tile, Finset.mem_Ico] at h
    exact hs (Nat.div_eq_of_lt_le h.1 h.2).symm
  have hJs : ∀ s₀, ∀ s ∈ J s₀, tile r u s ⊆ (Finset.range n).erase i₀ := fun s₀ s hs x hx => by
    obtain ⟨hs1, hs2⟩ := Finset.mem_erase.1 hs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.1 hs2
    have hst : s + 1 ≤ t := by rw [← hj]; exact Nat.mod_lt _ (by omega)
    refine Finset.mem_erase.2 ⟨fun h => hnot s hs1 (h ▸ hx), Finset.mem_range.2 ?_⟩
    rw [tile, Finset.mem_Ico] at hx
    exact hx.2.trans_le ((Nat.le_div_iff_mul_le hl).1 hst)
  calc _ ≤ exP p ((Finset.range n).erase i₀) (fun U => ∑ s₀ ∈ Finset.range t,
          ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s))) := by
        have hnn : ∀ U s₀, 0 ≤ ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s)) :=
          fun U s₀ => Finset.prod_nonneg fun s _ => sub_nonneg.2 (ind_le_one' _)
        refine ex_mono fun U hU => ind_le' (Finset.sum_nonneg fun _ _ => hnn _ _) ?_
        intro h
        unfold CondTiles at h
        push Not at h
        obtain ⟨s₀, hs₀, h⟩ := h
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun s₀ => ∏ s ∈ J s₀, (1 - ind (Marked (U ∩ tile r u s) r u s)))
          (fun _ _ => hnn _ _) (Finset.mem_range.2 hs₀))
        refine (Finset.prod_eq_one fun s hs => ?_).symm
        obtain ⟨hs1, hs2⟩ := Finset.mem_erase.1 hs
        obtain ⟨j, hj, hjs⟩ := Finset.mem_image.1 hs2
        rw [ind_neg', sub_zero]
        intro hM
        refine h j (by have := Finset.mem_range.1 hj; omega) ?_
        have hjs' : (s₀ + j) % t = s := hjs
        rw [hjs']
        refine marked_congr ?_ hM
        rw [Finset.insert_inter_of_notMem (hnot s hs1), Finset.inter_assoc, Finset.inter_self]
    _ ≤ ∑ s₀ ∈ Finset.range t, (1 - markedLow δ r u) ^ M₀ := by
        rw [ex_sum]
        refine Finset.sum_le_sum fun s₀ _ => ?_
        rw [ex_prod (J s₀) (tile r u) (fun s V => 1 - ind (Marked V r u s)) _
          (fun i _ j _ hij => tile_disjoint hij) (hJs s₀)]
        calc _ ≤ ∏ s ∈ J s₀, (1 - markedLow δ r u) := by
              refine Finset.prod_le_prod₀ (fun s _ => ?_) fun s _ => ?_
              · rw [bernoulliExpectation_one_sub]; linarith [hP1 s]
              · rw [bernoulliExpectation_one_sub]; linarith [hmk s]
          _ ≤ _ := by
              rw [Finset.prod_const]
              exact pow_le_pow_of_le_one (by linarith) (by linarith) (hJc s₀)
    _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n l)
          (pow_nonneg (by linarith) _)
end

section -- merged from Development.AutomorphicArithmetic.ThickFrames.TailLe
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.bernoulliExpectation_le_of_monotone (p : ℕ → ℝ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A : Finset ℕ) :
    ∀ f : Finset ℕ → ℝ, Monotone f → (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) →
      exP p A f ≤ GlobalTheory.RandomTops.ex δ A f := by
  induction A using Finset.induction_on with
  | empty =>
    intro f _ _
    rw [GlobalTheory.RandomTops.ex_empty]
    simp [exP]
  | insert a S ha ih =>
    intro f hf hp
    have hpS : ∀ b ∈ S, 0 ≤ p b ∧ p b ≤ δ := fun b hb => hp b (Finset.mem_insert_of_mem hb)
    obtain ⟨hpa0, hpa1⟩ := hp a (Finset.mem_insert_self _ _)
    have e1 := ih f hf hpS
    have e2 := ih (fun T => f (insert a T))
      (fun T U hTU => hf (Finset.insert_subset_insert a hTU)) hpS
    have e3 : GlobalTheory.RandomTops.ex δ S f ≤ GlobalTheory.RandomTops.ex δ S (fun T => f (insert a T)) :=
      GlobalTheory.RandomTops.ex_mono h0 h1 fun T _ => hf (Finset.subset_insert a T)
    rw [(UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec p).2.2.2.2.1 a S f ha, GlobalTheory.RandomTops.ex_insert ha]
    have k1 := mul_le_mul_of_nonneg_left e1 (show 0 ≤ 1 - p a by linarith)
    have k2 := mul_le_mul_of_nonneg_left e2 hpa0
    have k3 := mul_le_mul_of_nonneg_left e3 (show 0 ≤ δ - p a by linarith)
    linarith

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tail_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (A : Finset ℕ) (G K : ℕ), (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → A.card ≤ G →
      exP p A (fun T => ind (K ≤ T.card)) ≤ (G.choose K : ℝ) * δ ^ K ∧ exP p A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  intro p δ A G K hp h0 h1 hG
  have hmono : Monotone (fun T : Finset ℕ => ind (K ≤ T.card)) := by
    intro T U hTU
    have hc := Finset.card_le_card hTU
    simp only [ind]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have hle := UpperTheory.BernoulliSumsFrobeniusOrbits.bernoulliExpectation_le_of_monotone p δ h0 h1 A _ hmono hp
  exact ⟨le_trans hle (GlobalTheory.RandomTops.tail_le_choose h0 h1 hG K),
    le_trans hle (GlobalTheory.RandomTops.tail_le_binUpper h0 h1 hG K)⟩
end

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

private theorem ngl_ind_pos {q : Prop} (h : q) : ind q = 1 := by
  unfold ind
  exact if_pos h
private theorem ngl_ind_nonneg (q : Prop) : 0 ≤ ind q := by
  unfold ind
  split_ifs <;> norm_num
private theorem ngl_ind_le {q : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : q → 1 ≤ x) : ind q ≤ x := by
  unfold ind
  split_ifs with hq
  · exact h1 hq
  · exact h0

private theorem ngl_windows_le (p : ℕ → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (n i₀ L K K' : ℕ)
    (hK : K' ≤ K) (b : ℝ)
    (hb : ∀ A : Finset ℕ, A.card ≤ L → exP p A (fun T => ind (K' ≤ T.card)) ≤ b) :
    exP p ((Finset.range n).erase i₀)
      (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K)) ≤ n * b := by
  obtain ⟨_, _, h_sum, h_mono, _, h_restr, _⟩ := expectation_spec p
  calc exP p ((Finset.range n).erase i₀)
        (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K))
      ≤ exP p ((Finset.range n).erase i₀) (fun U => ∑ i ∈ Finset.range n,
          ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card)) := by
        apply h_mono _ _ _ (fun a _ => hp a)
        intro U hU
        apply ngl_ind_le (Finset.sum_nonneg (fun i _ => ngl_ind_nonneg _))
        intro hq
        push_neg at hq
        obtain ⟨i, hi, hc⟩ := hq
        have hsub : U ∩ (window n i L ∩ (Finset.range n).erase i₀) = U ∩ window n i L := by
          ext x
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨h1, h2, _⟩
            exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, h2, hU h1⟩
        have hle : (insert i₀ U ∩ window n i L).card ≤ (U ∩ window n i L).card + 1 := by
          calc (insert i₀ U ∩ window n i L).card ≤ (insert i₀ (U ∩ window n i L)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_inter, Finset.mem_insert] at hx ⊢
                rcases hx with ⟨h1 | h1, h2⟩
                · exact Or.inl h1
                · exact Or.inr ⟨h1, h2⟩
            _ ≤ (U ∩ window n i L).card + 1 := Finset.card_insert_le _ _
        have hK'' : K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card := by
          rw [hsub]
          omega
        calc (1 : ℝ) = ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card) :=
              (ngl_ind_pos hK'').symm
          _ ≤ ∑ j ∈ Finset.range n,
                ind (K' ≤ (U ∩ (window n j L ∩ (Finset.range n).erase i₀)).card) :=
              Finset.single_le_sum (f := fun j =>
                ind (K' ≤ (U ∩ (window n j L ∩ (Finset.range n).erase i₀)).card))
                (fun j _ => ngl_ind_nonneg _) (Finset.mem_range.2 hi)
    _ = ∑ i ∈ Finset.range n, exP p ((Finset.range n).erase i₀)
          (fun U => ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card)) :=
        h_sum _ _ (fun i U => ind (K' ≤ (U ∩ (window n i L ∩ (Finset.range n).erase i₀)).card))
    _ = ∑ i ∈ Finset.range n, exP p (window n i L ∩ (Finset.range n).erase i₀)
          (fun T => ind (K' ≤ T.card)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_restr _ _ (fun T => ind (K' ≤ T.card)) Finset.inter_subset_right
    _ ≤ ∑ _i ∈ Finset.range n, b := by
        apply Finset.sum_le_sum
        intro i _
        apply hb
        calc (window n i L ∩ (Finset.range n).erase i₀).card ≤ (window n i L).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ ≤ (Finset.range L).card := by
              unfold window
              exact Finset.card_image_le
          _ = L := Finset.card_range L
    _ = n * b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n L₂ K r u M₀ G' N₁ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁)) ≤
        n * (L₂.choose K : ℝ) * δ ^ K + n * (1 - markedLow δ r u) ^ M₀ + n * binUpper G' δ (N₁ - 1) := by
  intro p δ n L₂ K r u M₀ G' N₁ i₀ hp hδ0 hδ1 hu hn
  obtain ⟨_, h_add, _, h_mono, _, _, _⟩ := expectation_spec p
  have hp1 : ∀ a, 0 ≤ p a ∧ p a ≤ 1 := fun a =>
    ⟨le_trans (by positivity) (hp a).1, le_trans (hp a).2 hδ1⟩
  have hpδ : ∀ (A : Finset ℕ), ∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ := fun A a _ => ⟨(hp1 a).1, (hp a).2⟩
  have hA : exP p ((range n).erase i₀) (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
      ≤ n * ((L₂.choose K : ℝ) * δ ^ K) :=
    ngl_windows_le p hp1 n i₀ L₂ K K le_rfl _
      (fun A hA => (tail_le p δ A L₂ K (hpδ A) hδ0 hδ1 hA).1)
  have hI : exP p ((range n).erase i₀) (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁))
      ≤ n * binUpper G' δ (N₁ - 1) :=
    ngl_windows_le p hp1 n i₀ G' N₁ (N₁ - 1) (Nat.sub_le _ _) _
      (fun A hA => (tail_le p δ A G' (N₁ - 1) (hpδ A) hδ0 hδ1 hA).2)
  have hT := tiles_le p δ n r u M₀ i₀ hp hδ0 hδ1 hu hn
  have hsplit : exP p ((range n).erase i₀)
        (fun U => ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁))
      ≤ exP p ((range n).erase i₀) (fun U => (ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
          + ind (¬ CondIntervals n (insert i₀ U) G' N₁)) := by
    apply h_mono _ _ _ (fun a _ => hp1 a)
    intro U _
    have e1 := ngl_ind_nonneg (¬ CondA n (insert i₀ U) L₂ K)
    have e2 := ngl_ind_nonneg (¬ CondTiles n (insert i₀ U) r u M₀)
    have e3 := ngl_ind_nonneg (¬ CondIntervals n (insert i₀ U) G' N₁)
    apply ngl_ind_le (by linarith)
    intro hq
    unfold GoodOrbitIntervalTileCondition at hq
    by_cases ha : CondA n (insert i₀ U) L₂ K
    · by_cases hb : CondTiles n (insert i₀ U) r u M₀
      · have hc : ¬ CondIntervals n (insert i₀ U) G' N₁ := fun hc => hq ⟨ha, hb, hc⟩
        rw [ngl_ind_pos hc]
        linarith
      · rw [ngl_ind_pos hb]
        linarith
    · rw [ngl_ind_pos ha]
      linarith
  have hsum : exP p ((range n).erase i₀) (fun U => (ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
          + ind (¬ CondIntervals n (insert i₀ U) G' N₁))
      = exP p ((range n).erase i₀) (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
        + exP p ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))
        + exP p ((range n).erase i₀) (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁)) := by
    rw [h_add _ (fun U => ind (¬ CondA n (insert i₀ U) L₂ K)
          + ind (¬ CondTiles n (insert i₀ U) r u M₀))
        (fun U => ind (¬ CondIntervals n (insert i₀ U) G' N₁)),
      h_add _ (fun U => ind (¬ CondA n (insert i₀ U) L₂ K))
        (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))]
  rw [hsum] at hsplit
  have hA' : (n : ℝ) * ((L₂.choose K : ℝ) * δ ^ K) = n * (L₂.choose K : ℝ) * δ ^ K := by ring
  linarith
end

section -- merged from Development.AutomorphicArithmetic.ThickFrames.orbitSum
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

namespace UpperTheory.BernoulliSumsFrobeniusOrbits

private lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) =
      pw (fun i => p (f i)) S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else p a with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - p a with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = pw (fun i => p (f i)) S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [pw, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [pw]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

private lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (F : Finset β → ℝ) :
    ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T)) =
      ∑ S : Finset β, pw (fun i => p (f i)) S * F S := by
  calc ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T))
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) * F S := by
        refine sum_congr rfl fun T _ => ?_
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [← sum_mul, fibre_sum p f hf S]

private lemma fin_sum_eq (n : ℕ) (q : ℕ → ℝ) (F : Finset ℕ → ℝ) :
    (∑ S : Finset (Fin n), pw (fun i : Fin n => q i) S * F (S.map Fin.valEmbedding)) =
      exP q (range n) F := by
  unfold exP
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have e : range n \ S.map Fin.valEmbedding = (univ \ S).map Fin.valEmbedding := by
      ext x
      simp only [mem_sdiff, mem_range, mem_map, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i.2, ?_⟩
        rintro ⟨j, hj, hji⟩
        exact hi (Fin.ext hji ▸ hj)
    rw [e, prod_map, prod_map]
    rfl

private lemma bernoulliExpectation_mem_and (q : ℕ → ℝ) {S : Finset ℕ} {i₀ : ℕ} (hm : i₀ ∈ S) (A : Finset ℕ → Prop) :
    exP q S (fun T => ind (i₀ ∈ T ∧ A T)) =
      q i₀ * exP q (S.erase i₀) (fun U => ind (A (insert i₀ U))) := by
  unfold exP
  conv_lhs => rw [← Finset.insert_erase hm]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase _ _), Finset.sum_eq_zero, zero_add, mul_sum]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    have e : insert i₀ (S.erase i₀) \ insert i₀ T = S.erase i₀ \ T := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    rw [e, prod_insert hT']
    simp only [mem_insert_self, true_and]
    ring
  · intro T hT
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    simp [ind, hT']

end UpperTheory.BernoulliSumsFrobeniusOrbits

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum :
    ∀ (α : Type) [Fintype α] [DecidableEq α] [AddCommGroup α] (p : α → ℝ) (b h t : α), (∃ i : ℕ, b + i • h = t) →
      ∀ A : Finset ℕ → Prop, ∃ i₀ < addOrderOf h, b + i₀ • h = t ∧
        ∑ T : Finset α, pw p T * ind (t ∈ T ∧ A ((univ.filter (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)) =
          p t * exP (fun i => p (b + i • h)) ((range (addOrderOf h)).erase i₀) (fun U => ind (A (insert i₀ U))) := by
  intro α _ _ _ p b h t ht A
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  have ht : b + (i % addOrderOf h) • h = t := by rw [mod_addOrderOf_nsmul, hi]
  refine ⟨i % addOrderOf h, hlt, ht, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  have h1 := bernoulliExpectation_mem_and (fun i => p (b + i • h)) (mem_range.2 hlt) A
  rw [ht] at h1
  rw [← h1, ← fin_sum_eq, ← marginal p _ hinj
    (fun S => ind (i % addOrderOf h ∈ S.map Fin.valEmbedding ∧ A (S.map Fin.valEmbedding)))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ i % addOrderOf h ∈ (univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding := by
    rw [show i % addOrderOf h = Fin.valEmbedding (⟨_, hlt⟩ : Fin (addOrderOf h)) from rfl,
      Finset.mem_map']
    simp [hi]
  simp only [this]
end

section -- merged from Development.AutomorphicArithmetic.ThickFrames.SharesOfCounts
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts :
    ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (T : Finset A) (δ η D : ℝ),
      0 < δ → η ≤ 1 → 0 ≤ D → 4 * A0.index * D ≤ η * (δ * Nat.card A0) →
      (∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * Nat.card A0| ≤ D) →
      δ * Fintype.card A / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card A ∧
        ∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (T.card : ℝ)| ≤ η * (T.card : ℝ) := by
  intro A _ _ _ A0 T δ η D hδ hη hD hDη hc
  set m : ℕ := A0.index with hm_def
  set n : ℕ := Nat.card A0 with hn_def
  have hm : (1:ℝ) ≤ m := by
    have h0 : A0.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hn : (1:ℝ) ≤ n := by
    have h0 : 0 < Nat.card A0 := Nat.card_pos
    exact_mod_cast h0
  have hA : (Fintype.card A : ℝ) = m * n := by
    have h1 : n * m = Fintype.card A := by
      rw [hn_def, hm_def, A0.card_mul_index, Nat.card_eq_fintype_card]
    rw [← h1]
    push_cast
    ring
  have hcardA0 : (Finset.univ.filter fun x : A => x ∈ A0).card = n := by
    rw [hn_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsumN : ∑ γ : A, (T.filter fun t => t - γ ∈ A0).card = T.card * n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have inner : ∀ t : A, (∑ γ : A, if t - γ ∈ A0 then 1 else 0) = n := by
      intro t
      have h2 := Equiv.sum_comp (Equiv.subLeft t) (fun x => if x ∈ A0 then (1:ℕ) else 0)
      simp only [Equiv.subLeft_apply] at h2
      rw [h2, ← Finset.card_filter]
      exact hcardA0
    rw [Finset.sum_congr rfl (fun t _ => inner t), Finset.sum_const, smul_eq_mul]
  have hsum : (∑ γ : A, ((T.filter fun t => t - γ ∈ A0).card : ℝ)) = n * T.card := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) hsumN
    push_cast at h3
    rw [h3]
    ring
  have hf : (∑ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)) = (3 * m + 1) / 4 * δ * n * n := by
    have hpt : ∀ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)
        = 3 / 4 * δ * n + (if γ ∈ A0 then δ / 4 * n else 0) := by
      intro γ
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun γ _ => hpt γ), Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, hcardA0, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hA]
    ring
  have hdiff : |(n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n| ≤ m * n * D := by
    rw [← hsum, ← hf, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ : A, D := Finset.sum_le_sum fun γ _ => hc γ
      _ = m * n * D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hA]
  have hn0 : (0:ℝ) < n := by linarith
  have hT : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := by
    have he : (n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n = n * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) := by ring
    rw [he, abs_mul, abs_of_pos hn0] at hdiff
    have h4 : (n:ℝ) * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ n * (m * D) := by linarith
    exact le_of_mul_le_mul_left h4 hn0
  have hδn : 0 < δ * n := mul_pos hδ hn0
  have hηδ : η * (δ * n) ≤ δ * n := mul_le_of_le_one_left (le_of_lt hδn) hη
  have hmD : 0 ≤ (m:ℝ) * D := mul_nonneg (by linarith) hD
  have hmδn : 0 ≤ (m:ℝ) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  have hm1δn : 0 ≤ ((m:ℝ) - 1) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  rw [abs_le] at hT
  have hX1 : 3 * m * δ * n / 4 ≤ (T.card : ℝ) := by nlinarith
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    have h5 : η * (δ * n) < 0 := mul_neg_of_neg_of_pos hneg hδn
    linarith
  have hηX : 3 * D ≤ η * T.card := by
    have hmm : 0 ≤ D * ((m:ℝ) * m - 1) := mul_nonneg hD (by nlinarith)
    calc 3 * D ≤ 3 * m * m * D := by nlinarith
      _ = (3 * m / 4) * (4 * m * D) := by ring
      _ ≤ (3 * m / 4) * (η * (δ * n)) := mul_le_mul_of_nonneg_left hDη (by positivity)
      _ = η * (3 * m * δ * n / 4) := by ring
      _ ≤ η * T.card := mul_le_mul_of_nonneg_left hX1 hη0
  have hK : (0:ℝ) < 3 * m + 1 := by linarith
  have key : ∀ w c : ℝ, 0 ≤ w → w ≤ 4 → |c - w * δ * n / 4| ≤ D →
      |c - w / (3 * m + 1) * T.card| ≤ η * T.card := by
    intro w c hw0 hw4 hcw
    have hE : w / (3 * m + 1) * (T.card : ℝ)
        = w * δ * n / 4 + w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1) := by
      field_simp
      ring
    have h1 : |w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1)| ≤ 2 * D := by
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hK, div_le_iff₀ hK]
      have habs : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := abs_le.mpr hT
      calc w * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ 4 * (m * D) :=
            mul_le_mul hw4 habs (abs_nonneg _) (by norm_num)
        _ ≤ 2 * D * (3 * m + 1) := by nlinarith
    rw [hE]
    rw [abs_le] at hcw h1 ⊢
    constructor <;> linarith [hcw.1, hcw.2, h1.1, h1.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; nlinarith
  · intro γ
    have hcγ := hc γ
    by_cases hγ : γ ∈ A0
    · simp only [if_pos hγ] at hcγ ⊢
      have e : (4:ℝ) * δ * n / 4 = δ * n := by ring
      exact key 4 _ (by norm_num) le_rfl (by rw [e]; exact hcγ)
    · simp only [if_neg hγ] at hcγ ⊢
      have e : (3:ℝ) * δ * n / 4 = 3 / 4 * δ * n := by ring
      exact key 3 _ (by norm_num) (by norm_num) (by rw [e]; exact hcγ)
end

section -- merged from Development.AutomorphicArithmetic.ThickFrames.select
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

private theorem sel_moment {α : Type} [DecidableEq α] (p g : α → ℝ) (S : Finset α) (c : ℝ) :
    ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) * (c + ∑ a ∈ T, g a) ^ 2 =
      (c + ∑ a ∈ S, g a * p a) ^ 2 + ∑ a ∈ S, g a ^ 2 * (p a * (1 - p a)) := by
  induction S using Finset.induction_on generalizing c with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_powerset_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ insert x S \ T, (1 - p a)) *
          (c + ∑ a ∈ T, g a) ^ 2 =
        (1 - p x) * ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) *
          (c + ∑ a ∈ T, g a) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.insert_sdiff_of_notMem _ hxT,
        Finset.prod_insert (fun h => hx (Finset.mem_sdiff.1 h).1)]
      ring
    have h2 : ∑ T ∈ S.powerset, ((∏ a ∈ insert x T, p a) *
          ∏ a ∈ insert x S \ insert x T, (1 - p a)) * (c + ∑ a ∈ insert x T, g a) ^ 2 =
        p x * ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) *
          ((c + g x) + ∑ a ∈ T, g a) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hx,
        Finset.prod_insert hxT, Finset.sum_insert hxT]
      ring
    rw [h1, h2, ih, ih]
    ring

private theorem sel_moment' {α : Type} [Fintype α] [DecidableEq α] (p g : α → ℝ) (c : ℝ) :
    ∑ T : Finset α, pw p T * (c + ∑ a ∈ T, g a) ^ 2 =
      (c + ∑ a, g a * p a) ^ 2 + ∑ a, g a ^ 2 * (p a * (1 - p a)) := by
  have := sel_moment p g univ c
  rw [Finset.powerset_univ] at this
  exact this

private theorem sel_exists {γ : Type} [Fintype γ] (w F : γ → ℝ) (hw : ∀ T, 0 ≤ w T)
    (h1 : ∑ T, w T = 1) : ∃ T, 0 < w T ∧ F T ≤ ∑ U, w U * F U := by
  by_contra hc
  push Not at hc
  obtain ⟨T₀, hT₀⟩ : ∃ T, 0 < w T := by
    by_contra h
    push Not at h
    have : ∑ T, w T ≤ 0 := Finset.sum_nonpos fun T _ => h T
    linarith
  have : ∑ T, w T * (∑ U, w U * F U) < ∑ T, w T * F T := by
    refine Finset.sum_lt_sum (fun T _ => ?_) ⟨T₀, Finset.mem_univ _, ?_⟩
    · rcases (hw T).eq_or_lt with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (hc T h).le h.le
    · exact mul_lt_mul_of_pos_left (hc T₀ hT₀) hT₀
  rw [← Finset.sum_mul, h1, one_mul] at this
  exact lt_irrefl _ this

private theorem sel_ncard {α : Type} [Fintype α] (P : α → Prop) :
    (({t | P t}.ncard : ℕ) : ℝ) = ∑ t, ind (P t) := by
  classical
  have : {t | P t} = ((univ.filter P : Finset α) : Set α) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold ind
  by_cases h : P t <;> simp [h]

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.select :
    ∀ (α κ ι : Type) [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] (cl : α → κ) (p : α → ℝ) (δ β D : ℝ)
        (I : Finset ι) (ω : ι → ℝ) (BAD : ι → α → Finset α → Prop),
      (∀ a, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 0 ≤ β → (∀ i, 0 ≤ ω i) → 0 < D → 2 * δ * Fintype.card α ≤ D ^ 2 →
      (∀ i ∈ I, ∀ t, ∑ T : Finset α, pw p T * ind (t ∈ T ∧ BAD i t T) ≤ β * δ) →
      ∃ T : Finset α, (∀ c : κ, |((T.filter fun a => cl a = c).card : ℝ) - ∑ a ∈ univ.filter (fun a => cl a = c), p a| ≤ D) ∧
        ∑ i ∈ I, ω i * (({t | t ∈ T ∧ BAD i t T}.ncard : ℕ) : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ i ∈ I, ω i := by
  intro α κ ι _ _ _ _ cl p δ β D I ω BAD hp hδ hδ1 hβ hω hD hD2 hbad
  have hw : ∀ T : Finset α, 0 ≤ pw p T := fun T =>
    mul_nonneg (Finset.prod_nonneg fun a _ => (hp a).1)
      (Finset.prod_nonneg fun a _ => by linarith [(hp a).2])
  have h1 : ∑ T : Finset α, pw p T = 1 := by
    simpa using sel_moment' p (fun _ => 0) 1
  set Y : κ → Finset α → ℝ := fun c T =>
    ((T.filter fun a => cl a = c).card : ℝ) - ∑ a ∈ univ.filter (fun a => cl a = c), p a with hY
  set B : Finset α → ℝ := fun T =>
    ∑ i ∈ I, ω i * (({t | t ∈ T ∧ BAD i t T}.ncard : ℕ) : ℝ) with hB
  set m : ℝ := β * δ * Fintype.card α * ∑ i ∈ I, ω i with hm
  have hm0 : 0 ≤ m := by
    have : 0 ≤ ∑ i ∈ I, ω i := Finset.sum_nonneg fun i _ => hω i
    positivity
  have hB0 : ∀ T, 0 ≤ B T := fun T =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hω i) (Nat.cast_nonneg _)
  have hEY : ∀ c, ∑ T, pw p T * Y c T ^ 2 ≤ ∑ a, if cl a = c then δ else 0 := by
    intro c
    have h := sel_moment' p (fun a => if cl a = c then 1 else 0)
      (-∑ a ∈ univ.filter (fun a => cl a = c), p a)
    have e1 : ∀ T : Finset α, Y c T = -∑ a ∈ univ.filter (fun a => cl a = c), p a +
        ∑ a ∈ T, (if cl a = c then (1 : ℝ) else 0) := by
      intro T
      simp only [hY]
      rw [Finset.card_filter]
      push_cast
      ring
    have e2 : ∑ a, (if cl a = c then (1 : ℝ) else 0) * p a =
        ∑ a ∈ univ.filter (fun a => cl a = c), p a := by
      rw [Finset.sum_filter]
      simp
    simp only [e1]
    rw [h, e2, neg_add_cancel, zero_pow two_ne_zero, zero_add]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs
    · nlinarith [(hp a).1, (hp a).2, sq_nonneg (p a)]
    · simp
  have hEX : ∑ T, pw p T * ∑ c, Y c T ^ 2 ≤ D ^ 2 / 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun c _ => hEY c).trans ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    linarith
  have hEB : ∑ T, pw p T * B T ≤ m := by
    simp only [hB, sel_ncard, Finset.mul_sum, hm]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.sum_comm]
    calc ∑ t, ∑ T, pw p T * (ω i * ind (t ∈ T ∧ BAD i t T))
        ≤ ∑ _t : α, ω i * (β * δ) := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hbad i hi t) (hω i))
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  obtain ⟨T, hT0, hT⟩ := sel_exists (pw p)
    (fun T => (∑ c, Y c T ^ 2) / D ^ 2 + B T / (4 * m)) hw h1
  have hD0 : 0 < D ^ 2 := by positivity
  have hE : ∑ U, pw p U * ((∑ c, Y c U ^ 2) / D ^ 2 + B U / (4 * m)) ≤ 1 := by
    have e : ∑ U, pw p U * ((∑ c, Y c U ^ 2) / D ^ 2 + B U / (4 * m)) =
        (∑ U, pw p U * ∑ c, Y c U ^ 2) / D ^ 2 + (∑ U, pw p U * B U) / (4 * m) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun U _ => by ring
    have a1 : (∑ U, pw p U * ∑ c, Y c U ^ 2) / D ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ hD0]; linarith
    have a2 : (∑ U, pw p U * B U) / (4 * m) ≤ 1 / 2 :=
      div_le_of_le_mul₀ (by positivity) (by norm_num) (by linarith)
    rw [e]; linarith
  have hT1 := hT.trans hE
  have n1 : 0 ≤ (∑ c, Y c T ^ 2) / D ^ 2 :=
    div_nonneg (Finset.sum_nonneg fun c _ => sq_nonneg _) hD0.le
  have n2 : 0 ≤ B T / (4 * m) := div_nonneg (hB0 T) (by positivity)
  refine ⟨T, fun c => ?_, ?_⟩
  · have a1 : (∑ c, Y c T ^ 2) / D ^ 2 ≤ 1 := by linarith
    rw [div_le_one hD0] at a1
    have a2 : Y c T ^ 2 ≤ ∑ c, Y c T ^ 2 :=
      Finset.single_le_sum (f := fun c => Y c T ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
    exact abs_le_of_sq_le_sq (a2.trans a1) hD.le
  · have key : B T ≤ 4 * m := by
      rcases hm0.eq_or_lt with h | h
      · have a1 : pw p T * B T ≤ ∑ U, pw p U * B U :=
          Finset.single_le_sum (f := fun U => pw p U * B U)
            (fun U _ => mul_nonneg (hw U) (hB0 U)) (Finset.mem_univ T)
        have a2 : pw p T * B T ≤ 0 := by linarith
        have a3 : B T ≤ 0 := by
          by_contra hc
          push Not at hc
          linarith [mul_pos hT0 hc]
        linarith
      · have a1 : B T / (4 * m) ≤ 1 := by linarith
        rwa [div_le_one (by positivity)] at a1
    calc _ = B T := rfl
      _ ≤ 4 * m := key
      _ = _ := by rw [hm]; ring
end

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

private theorem tg_num (x eps Co δ N o n0 : ℝ) (he : 0 < eps) (hx : 1 ≤ x) (hbig : 64 * Co ^ 4 ≤ x ^ eps)
    (hδe : δ = x ^ (-(eps / 8))) (hN : x ^ (2 + 8 * eps) / 2 ≤ N) (ho1 : 1 ≤ o) (ho : o ≤ Co) (hn : o * n0 = N) :
    4 * o * Real.sqrt (2 * δ * N) ≤ x⁻¹ * (δ * n0) := by
  have hx0 : 0 < x := by linarith
  have hδ : 0 < δ := by rw [hδe]; positivity
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have ho0 : 0 < o := by linarith
  have hn0 : n0 = N / o := by rw [← hn]; field_simp
  have h1 : x ^ 2 * x ^ eps ≤ δ * x ^ (2 + 8 * eps) := by
    rw [hδe, ← Real.rpow_add hx0, ← Real.rpow_two, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : o ^ 4 ≤ Co ^ 4 := pow_le_pow_left₀ ho0.le ho 4
  have h3 : 32 * o ^ 4 * x ^ 2 ≤ δ * N := by
    have a1 := mul_le_mul_of_nonneg_left hN hδ.le
    have a2 : x ^ 2 * (64 * o ^ 4) ≤ x ^ 2 * x ^ eps :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h4 : Real.sqrt (2 * δ * N) ≤ δ * N / (4 * o ^ 2 * x) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ δ * N)
    calc 2 * δ * N * (4 * o ^ 2 * x) ^ 2 = δ * N * (32 * o ^ 4 * x ^ 2) := by ring
      _ ≤ δ * N * (δ * N) := this
      _ = _ := by ring
  calc 4 * o * Real.sqrt (2 * δ * N) ≤ 4 * o * (δ * N / (4 * o ^ 2 * x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [hn0]; field_simp

private theorem tg_class_sum (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A)
    (u v : ℝ) (γ : A) :
    ∑ a ∈ univ.filter (fun a : A => a - γ ∈ A0), (if a ∈ A0 then u else v) =
      (if γ ∈ A0 then u else v) * Nat.card A0 := by
  have hc : (univ.filter (fun a : A => a - γ ∈ A0)).card = Nat.card A0 := by
    have e : {a : A // a - γ ∈ A0} ≃ A0 :=
      { toFun := fun a => ⟨a.1 - γ, a.2⟩
        invFun := fun b => ⟨b.1 + γ, by simp⟩
        left_inv := fun a => by ext; simp
        right_inv := fun b => by ext; simp }
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl (g := fun _ => if γ ∈ A0 then u else v), Finset.sum_const, nsmul_eq_mul, hc, mul_comm]
  intro a ha
  rw [Finset.mem_filter] at ha
  have hiff : a ∈ A0 ↔ γ ∈ A0 := by
    constructor
    · intro h
      have := A0.sub_mem h ha.2
      simpa using this
    · intro h
      have := A0.add_mem ha.2 h
      simpa using this
  simp only [hiff]

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsGroup :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (Fintype.card A : ℝ) → (Fintype.card A : ℝ) ≤ Co * x ^ hE eps → (A0.index : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : A → A → A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset A, dE eps x * Fintype.card A / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * Fintype.card A ∧
        (∀ γ : A, |((TT.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (TT.card : ℝ)| ≤ x ^ (-1 + eps) * (TT.card : ℝ)) ∧
        ∑ p ∈ PP, ω p * (({t : A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * Fintype.card A * ∑ p ∈ PP, ω p := by
  intro eps Co Lb he
  obtain ⟨Cb, x₀, hCb, hnum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms eps Co Lb he
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop he).eventually_ge_atTop (64 * Co ^ 4))
  refine ⟨Cb, max x₀ (max x₁ 1), hCb, ?_⟩
  intro x hx A _ _ _ A0 L₂ hlo hhi hidx hL bs hbs PP hp ω hω hPP
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hδ : 0 < dE eps x := Real.rpow_pos_of_pos hx0 _
  have hδ1 : dE eps x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hN0 : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hβ : 0 ≤ Cb * x ^ (-2 : ℝ) := by positivity
  have hp1 : ∀ a : A, 3 / 4 * dE eps x ≤ (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ∧
      (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ≤ dE eps x := by
    intro a
    split_ifs <;> constructor <;> linarith
  have hD : 0 < Real.sqrt (2 * dE eps x * Fintype.card A) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨T, hT1, hT2⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.select A (A ⧸ A0) ℕ (fun a => (a : A ⧸ A0))
    (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x) (Cb * x ^ (-2 : ℝ))
    (Real.sqrt (2 * dE eps x * Fintype.card A)) PP ω
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (KE eps) (rE eps)
      (dE eps x) (hE eps) x)
    (fun a => ⟨le_trans (by positivity) (hp1 a).1, (hp1 a).2⟩) hδ.le hδ1 hβ hω hD
    (le_of_eq (Real.sq_sqrt (by positivity)).symm) (by
      intro p hpp t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ Co * x ^ hE eps :=
        le_trans (Nat.cast_le.mpr addOrderOf_le_card_univ) hhi
      obtain ⟨h1, h2⟩ := hnum x hxx0 (addOrderOf (hp p)) L₂ (hPP p hpp) hn hL
      obtain ⟨i₀, _, _, hsum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum A
        (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (KE eps) (rE eps)
          (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
          (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU (dE eps x) := Nat.ceil_pos.mpr (by positivity)
      have h3 := UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
        (fun i => if bs (hp p) t + i • hp p ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x)
        (addOrderOf (hp p)) L₂ (KE eps) (rE eps)
        (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
        (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
        (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x) i₀ (fun i => hp1 _) hδ.le hδ1 hu h1
      refine le_trans (le_of_eq hsum) ?_
      rw [mul_comm (Cb * x ^ (-2 : ℝ))]
      exact le_trans (mul_le_mul_of_nonneg_left (h3.trans h2)
        (le_trans (by positivity) (hp1 t).1)) (mul_le_mul_of_nonneg_right (hp1 t).2 hβ))
  have hidx1 : (1 : ℝ) ≤ A0.index := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 AddSubgroup.index_ne_zero_of_finite
  have hmul : (A0.index : ℝ) * Nat.card A0 = Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast A0.index_mul_card
  have hnumD := tg_num x eps Co (dE eps x) (Fintype.card A) A0.index (Nat.card A0) he hx1
    (hx₁ x hxx1) rfl hlo hidx1 hidx hmul
  obtain ⟨hS1, hS2, hS3⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts A A0 T (dE eps x) x⁻¹
    (Real.sqrt (2 * dE eps x * Fintype.card A)) hδ (inv_le_one_of_one_le₀ hx1) hD.le hnumD (by
      intro γ
      have hc : ∀ a : A, ((a : A ⧸ A0) = (γ : A ⧸ A0)) ↔ a - γ ∈ A0 := fun a =>
        QuotientAddGroup.eq_iff_sub_mem
      have := hT1 (γ : A ⧸ A0)
      simp only [hc] at this
      rw [← tg_class_sum A A0 (dE eps x) (3 / 4 * dE eps x) γ]
      convert this)
  refine ⟨T, hS1, hS2, fun γ => le_trans (hS3 γ) ?_, hT2⟩
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
