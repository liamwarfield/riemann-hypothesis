module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SortGetDSpec
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightOfParts
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

def LetterDictionaryBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b →
    ∃ (n0 : ℕ) (od : Fin (segN X.F j) → Fin (segN X.F j)),
      HypT (segN X.F j) n0 r K (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
        (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p ∧
      (∀ μ dd, X.IsPATH p K j (X.restr j b) μ dd ↔
        IsPATHa (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) μ dd) ∧
      (∀ μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ,
        GoodA (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
          (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p μ →
        X.IsGood p K j (X.restr j b) μ) ∧
      ((rkA r K n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) : ℕ) : ℝ) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ∧
      Real.exp (11 * ((segN X.F j : ℕ) : ℝ) ^ 2 * ell0 (segN X.F j) X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤
        1 / X.a ^ (X.Ns ^ 2)

theorem good_path_weight_of_parts (C₀ : ℝ) (ha : PathWeightEqRank) (hT : LemT) (he : LetterDictionaryBounds C₀) : GoodPathWeight C₀ := by
  intro p n' r K _ _ _ X hX hCLa hCk j b hb
  obtain ⟨n0, od, hH, hPATH, hGood, hrk, hexp⟩ := he p n' r K X hX hCLa hCk j b hb
  obtain ⟨hfin, hcard⟩ := hT (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  obtain ⟨hfinA, -⟩ := ha (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  let S : Set ((Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))) :=
    {q | ∃ dd, X.IsPATH p K j (X.restr j b) q.1 dd ∧ X.IsGood p K j (X.restr j b) q.1 ∧ IsSt (tanPart q.1) q.2}
  have hSA : S ⊆ SAll (r := r) (K := K) (segLL X.F j) n0
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) := by
    rintro q ⟨dd, hp, -, hs⟩
    exact ⟨⟨dd, (hPATH q.1 dd).mp hp⟩, hs⟩
  have hGS : SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p ⊆ S := by
    rintro q ⟨⟨dd, hp⟩, hg, hs⟩
    exact ⟨dd, (hPATH q.1 dd).mpr hp, hGood q.1 hg, hs⟩
  have hSfin : S.Finite := hfinA.subset hSA
  have hTS : Nat.card (X.Tset p K j (X.restr j b)) = S.ncard := Nat.card_coe_set_eq S
  refine ⟨hSfin.to_subtype, ?_⟩
  rw [hTS]
  have h1 : ((SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p).ncard : ℝ) ≤ S.ncard := by
    exact_mod_cast Set.ncard_le_ncard hGS hSfin
  rw [mul_assoc, ← hrk]
  refine le_trans ?_ (le_trans hcard h1)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) (j : ℤ) {L₁ N₁ : ℕ}

omit [NeZero r] in
theorem idx_card (i : Fin (segN F j)) : ((F.letters j).filter (· < segE F j i)).card = i.val := by
  classical
  have hIio : (Finset.univ.filter (· < i) : Finset (Fin (segN F j))) = Finset.Iio i := by
    ext k
    simp
  have hfe : (F.letters j).filter (· < segE F j i) =
      (Finset.univ.filter (· < i)).image
        (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_, by simp⟩
      exact (OrderIso.symm_apply_lt _).mpr hlt
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(((F.letters j).orderIsoOfFin rfl) k).2, ((F.letters j).orderIsoOfFin rfl).strictMono hk⟩
  have hinj : Function.Injective
      (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) :=
    fun a b h => (OrderIso.injective _) (Subtype.ext h)
  rw [hfe, Finset.card_image_of_injective _ hinj, hIio, Fin.card_Iio]

variable {F} {j}

omit [NeZero r] in
theorem fr_lt (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ i i', i < i' → i' < r → F.fr J i < F.fr J i' := by
  obtain ⟨_, _, hinc, _⟩ := id hV
  intro i i' h hr
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact lt_trans (ih h' (by omega)) (hinc J k hr)
    · subst h'
      exact hinc J i hr

omit [NeZero r] in
theorem fr_le (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (h : i ≤ i') (hr : i' < r) : F.fr J i ≤ F.fr J i' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · exact le_rfl
  · exact le_of_lt (fr_lt hV J i i' h' hr)

omit [NeZero r] in
theorem fr_inj (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (hi : i < r) (hi' : i' < r) (h : F.fr J i = F.fr J i') :
    i = i' := by
  rcases lt_trichotomy i i' with h1 | h1 | h1
  · exact absurd h (ne_of_lt (fr_lt hV J i i' h1 hi'))
  · exact h1
  · exact absurd h (ne_of_gt (fr_lt hV J i' i h1 hi))

theorem fr_prev_lt (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) (r - 1) < F.fr j 0 := by
  obtain ⟨_, _, _, hnext, _⟩ := id hV
  have := hnext (j - 1)
  rwa [sub_add_cancel] at this

theorem frj_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr j i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, fr_le hV j i' (r - 1) (by omega) (by omega)⟩, (hTT j i' h).1⟩
  have h1 := fr_le hV (j - 1) 0 (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 i' (by omega) h
  linarith

theorem frp_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr (j - 1) i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨fr_le hV (j - 1) 0 i' (by omega) h, ?_⟩, (hTT (j - 1) i' h).1⟩
  have h1 := fr_le hV (j - 1) i' (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 (r - 1) (by omega) (by omega)
  linarith

private theorem segE_mem_lemma_6 (J : ℤ) (i : Fin (segN F J)) : segE F J i ∈ F.letters J :=
  ((F.letters J).orderIsoOfFin rfl i).2

private theorem segE_lt_lemma_7 (J : ℤ) {a b : Fin (segN F J)} : segE F J a < segE F J b ↔ a < b := by
  unfold segE
  rw [Subtype.coe_lt_coe]
  exact OrderIso.lt_iff_lt _

private theorem segE_le_lemma_8 (J : ℤ) {a b : Fin (segN F J)} : segE F J a ≤ segE F J b ↔ a ≤ b := by
  unfold segE
  rw [Subtype.coe_le_coe]
  exact OrderIso.le_iff_le _

private theorem segE_surj_lemma_9 (J : ℤ) {x : ℤ} (hx : x ∈ F.letters J) : ∃ k : Fin (segN F J), segE F J k = x :=
  ⟨((F.letters J).orderIsoOfFin rfl).symm ⟨x, hx⟩, by unfold segE; simp⟩

private theorem segE_inj_lemma_10 (J : ℤ) : Function.Injective (segE F J) := by
  intro a b h
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt ((segE_lt_lemma_7 J).mpr h'))
  · exact h'
  · exact absurd h (ne_of_gt ((segE_lt_lemma_7 J).mpr h'))

private theorem gap_lemma_2 (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ k, k < r → ∀ x, F.fr J 0 ≤ x → x < F.fr J k →
    posOf n' x ∈ F.TT → ∃ m < k, x = F.fr J m := by
  obtain ⟨_, _, _, _, _, hgap, _⟩ := id hV
  intro k
  induction k with
  | zero =>
    intro _ x h1 h2 _
    exact absurd h2 (not_lt.mpr h1)
  | succ k ih =>
    intro hk x h1 h2 hx
    rcases lt_trichotomy x (F.fr J k) with h3 | h3 | h3
    · obtain ⟨m, hm, hxm⟩ := ih (by omega) x h1 h3 hx
      exact ⟨m, by omega, hxm⟩
    · exact ⟨k, by omega, h3⟩
    · exact absurd hx (hgap J k x hk h3 h2)

private theorem countW_lemma_3 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr (J - 1) i')).card = i' := by
  have hfe : (F.letters J).filter (· < F.fr (J - 1) i') = (Finset.range i').image (F.fr (J - 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hx, hlt⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV (J - 1) i' hi' x hx.1.1 hlt hx.2
      exact ⟨m, hm, hxm.symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨frp_mem hV J m (by omega), fr_lt hV (J - 1) m i' hm hi'⟩
  rw [hfe, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact fr_inj hV (J - 1) a b (by omega) (by omega) hab

private theorem countT_lemma_4 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (F.fr J i' ≤ ·)).card = r - i' := by
  have hfe : (F.letters J).filter (F.fr J i' ≤ ·) = (Finset.Ico i' r).image (F.fr J) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hle⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      rcases lt_or_eq_of_le hx.1.2 with hlt | heq
      · obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV J (r - 1) (by omega) x
          (le_trans (fr_le hV J 0 i' (Nat.zero_le _) hi') hle) hlt hx.2
        subst hxm
        refine ⟨m, ⟨?_, by omega⟩, rfl⟩
        by_contra hc
        exact absurd hle (not_le.mpr (fr_lt hV J m i' (by omega) hi'))
      · exact ⟨r - 1, ⟨by omega, by omega⟩, heq.symm⟩
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      exact ⟨frj_mem hV J m hm2, fr_le hV J i' m hm1 hm2⟩
  rw [hfe, Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha b hb hab
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
  exact fr_inj hV J a b ha.2 hb.2 hab

private theorem countTlt_lemma_5 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr J i')).card + (r - i') = (F.letters J).card := by
  rw [← countT_lemma_4 hV J i' hi']
  have e := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (F.fr J i' ≤ ·) (F.letters J))
  have hs : (F.letters J) \ (F.letters J).filter (F.fr J i' ≤ ·) = (F.letters J).filter (· < F.fr J i') := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, not_le.mp fun h' => h ⟨hy, h'⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun h' => absurd h'.2 (not_le.mpr h)⟩
  rw [hs] at e
  exact e

theorem idx_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr (j - 1) i') :
    i.val = i' := by
  have h1 := idx_card F j i
  rw [h, countW_lemma_3 hV j i' hi'] at h1
  exact h1.symm

theorem idx_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr j i') :
    i.val + (r - i') = segN F j := by
  have h1 := idx_card F j i
  rw [h] at h1
  have h2 := countTlt_lemma_5 hV j i' hi'
  rw [h1] at h2
  exact h2

theorem r_le_segN (hV : F.Valid L₁ N₁) (j : ℤ) : r ≤ segN F j := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := countT_lemma_4 hV j 0 hr0
  have h2 := Finset.card_filter_le (F.letters j) (F.fr j 0 ≤ ·)
  rw [h1] at h2
  unfold segN
  omega

theorem dict_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : Fin r) :
    segE F j i = F.fr j i'.val ↔ i.val = (segN F j - r) + i'.val := by
  have hr := r_le_segN hV j
  have hi' := i'.isLt
  constructor
  · intro h
    have := idx_tau hV i i'.val i'.isLt h
    omega
  · intro h
    obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j i'.val i'.isLt)
    have := idx_tau hV k i'.val i'.isLt hk
    have hki : k = i := by
      apply Fin.ext
      omega
    subst hki
    exact hk

theorem dict_early (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr := r_le_segN hV j
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j 0 hr0)
  have hkv := (dict_tau hV k ⟨0, hr0⟩).mp hk
  rw [← hk, segE_lt_lemma_7, Fin.lt_iff_val_lt_val, hkv]
  show i.val < segN F j - r + 0 ↔ i.val < segN F j - r
  omega

theorem dict_wE (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : i.val < r) : segE F j i = F.fr (j - 1) i.val := by
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frp_mem hV j i.val h)
  have hki : k = i := Fin.ext (idx_w hV k i.val h hk)
  subst hki
  exact hk

theorem dict_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) : F.IsW j (segE F j i) ↔ i.val < r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr := r_le_segN hV j
  have hw : segE F j ⟨r - 1, by omega⟩ = F.fr (j - 1) (r - 1) :=
    dict_wE hV _ (by show r - 1 < r; omega)
  unfold Frames.IsW
  rw [← hw, segE_le_lemma_8, Fin.le_iff_val_le_val]
  show i.val ≤ r - 1 ↔ i.val < r
  omega

theorem mem_LLset_iff (hV : F.Valid L₁ N₁) (x : ℤ) :
    x ∈ F.LLset j ↔ x ∈ F.letters j ∧ ¬ F.IsW j x ∧ x < F.fr j 0 := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := fr_le hV (j - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  have h2 := fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have h3 := fr_prev_lt hV j
  unfold Frames.LLset Frames.letters Frames.IsW
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc, not_le]
  constructor
  · rintro ⟨⟨ha, hb⟩, hT⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, hT⟩, ha, hb⟩
  · rintro ⟨⟨_, hT⟩, ha, hb⟩
    exact ⟨⟨ha, hb⟩, hT⟩

theorem dict_LL (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i ∈ F.LLset j ↔ r ≤ i.val ∧ i.val < segN F j - r := by
  rw [mem_LLset_iff hV, dict_w hV, dict_early hV]
  have hm := segE_mem_lemma_6 j i
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨not_lt.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hm, not_lt.mpr h1, h2⟩

theorem LLset_eq_image (hV : F.Valid L₁ N₁) (j : ℤ) :
    F.LLset j = (Finset.univ.filter fun i : Fin (segN F j) => r ≤ i.val ∧ i.val < segN F j - r).image (segE F j) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hxl := ((mem_LLset_iff hV x).mp hx).1
    obtain ⟨k, rfl⟩ := segE_surj_lemma_9 j hxl
    exact ⟨k, (dict_LL hV k).mp hx, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (dict_LL hV k).mpr hk

omit [NeZero n'] [NeZero r] in
theorem card_fin_range (N a b : ℕ) (hb : b ≤ N) :
    (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).card = b - a := by
  have hm : (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).map Fin.valEmbedding = Finset.Ico a b := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hy
      exact ⟨⟨y, by omega⟩, hy, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm, Nat.card_Ico]

theorem card_LLset (hV : F.Valid L₁ N₁) (j : ℤ) : (F.LLset j).card = segN F j - r - r := by
  rw [LLset_eq_image hV j, Finset.card_image_of_injective _ (segE_inj_lemma_10 j),
    card_fin_range _ _ _ (Nat.sub_le _ _)]

theorem two_r_le (hV : F.Valid L₁ N₁) (j : ℤ) : 2 * r ≤ segN F j - r := by
  obtain ⟨_, _, _, _, _, _, hLL, _⟩ := id hV
  have h1 := (hLL j).1
  rw [card_LLset hV j] at h1
  omega

theorem card_LLset_le (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (hi : r ≤ i.val) (hi2 : i.val < segN F j - r) :
    ((F.LLset j).filter (· ≤ segE F j i)).card = i.val + 1 - r := by
  have hiv := i.isLt
  rw [LLset_eq_image hV j]
  have hfe : ((Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < segN F j - r).image
      (segE F j)).filter (· ≤ segE F j i) =
      (Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < i.val + 1).image (segE F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hle⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val] at hle
      exact ⟨k, ⟨hk.1, by omega⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, ⟨hk.1, by omega⟩, rfl⟩, ?_⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val]
      omega
  rw [hfe, Finset.card_image_of_injective _ (segE_inj_lemma_10 j), card_fin_range _ _ _ (by omega)]

theorem dict_lateV (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : segN F j - r ≤ i.val + r) : Even (segE F j i) := by
  obtain ⟨_, _, _, _, hTT, _, hLL, _⟩ := id hV
  have hr := r_le_segN hV j
  have h2r := two_r_le hV j
  have hiv := i.isLt
  by_cases hi : segN F j - r ≤ i.val
  · have hi' : i.val - (segN F j - r) < r := by omega
    have he := (dict_tau hV i ⟨i.val - (segN F j - r), hi'⟩).mpr
      (by show i.val = segN F j - r + (i.val - (segN F j - r)); omega)
    rw [he]
    exact (hTT j _ hi').2
  · have hin : segE F j i ∈ F.LLset j := (dict_LL hV i).mpr ⟨by omega, by omega⟩
    have hcnt := card_LLset_le hV i (by omega) (by omega)
    have hcard := card_LLset hV j
    exact (((hLL j).2.1 _ hin) (Or.inr (by rw [hcnt, hcard]; omega))).1

end Dict

end Formalism.MainNotions.SelectionLemmas.Pf.TE
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem sort_getD_spec (s : Finset ℤ) (r : ℕ) (hr : 0 < r) (hrs : r ≤ s.card) :
    (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ∈ s ∧
      (s.filter ((s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ≤ ·)).card = r := by
  classical
  have hlen : (s.sort (· ≤ ·)).length = s.card := Finset.length_sort _
  have hk : (s.sort (· ≤ ·)).length - r < s.card := by omega
  set f := s.orderEmbOfFin rfl with hf
  have hget : (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 = f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ := by
    rw [hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem]
    · simp [Fin.getElem_fin]
    · omega
  rw [hget]
  refine ⟨Finset.orderEmbOfFin_mem s rfl _, ?_⟩
  have hset : s.filter (f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ ≤ ·) =
      (Finset.univ.filter (fun i : Fin s.card => (s.sort (· ≤ ·)).length - r ≤ i.val ∧ i.val < s.card)).map f.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hle⟩
      have hr : y ∈ Set.range f := by rw [hf, Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, ⟨f.le_iff_le.1 hle, i.isLt⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s rfl i, f.le_iff_le.2 hi.1⟩
  rw [hset, Finset.card_map, card_fin_range _ _ _ le_rfl]
  omega

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem oldest_spec (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) (hi : r ≤ i.val) :
    F.oldest j (segE F j i) ∈ F.letters j ∧ Even (F.oldest j (segE F j i)) ∧ F.oldest j (segE F j i) < segE F j i ∧
      ((F.letters j).filter fun z => F.oldest j (segE F j i) ≤ z ∧ z < segE F j i ∧ Even z).card = r := by
  classical
  set E := segE F j i with hE
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hlow : ∀ i' < r, F.fr (j - 1) i' < E := by
    intro i' hi'
    obtain ⟨k, hk⟩ := hsurj _ (frp_mem hV j i' hi')
    have hki := idx_w hV k i' hi' hk
    rw [← hk]
    apply hmono
    show k.val < i.val
    omega
  have hcard : r ≤ ((F.letters j).filter fun z => Even z ∧ z < E).card := by
    have hsub : (Finset.range r).image (F.fr (j - 1)) ⊆ (F.letters j).filter fun z => Even z ∧ z < E := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i', hi', rfl⟩ := hx
      simp only [Finset.mem_filter]
      exact ⟨frp_mem hV j i' hi', (hV.2.2.2.2.1 (j - 1) i' hi').2, hlow i' hi'⟩
    have hinj : Set.InjOn (F.fr (j - 1)) (Finset.range r) := fun a ha b hb h =>
      fr_inj hV _ a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
    calc r = ((Finset.range r).image (F.fr (j - 1))).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨hm, hc⟩ := sort_getD_spec ((F.letters j).filter fun z => Even z ∧ z < E) r
    (Nat.pos_of_ne_zero (NeZero.ne r)) hcard
  have hold : F.oldest j E = (((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).getD
      ((((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).length - r) 0 := rfl
  rw [hold]
  simp only [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  rw [Finset.filter_filter] at hc
  refine Eq.trans ?_ hc
  exact congrArg Finset.card (Finset.filter_congr (fun z _ => by tauto))

theorem exists_od (hV : F.Valid L₁ N₁) (j : ℤ) : ∃ od : Fin (segN F j) → Fin (segN F j), ∀ i, r ≤ i.val →
    segE F j (od i) = F.oldest j (segE F j i) ∧ od i < i ∧ (segLL F j).vec (od i) = true ∧
      (Finset.univ.filter fun l : Fin (segN F j) => od i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).card = r := by
  classical
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hmem : ∀ l, segE F j l ∈ F.letters j := fun l => by
    simp only [segE]
    exact Subtype.mem _
  have hex : ∀ i : Fin (segN F j), ∃ k, r ≤ i.val → segE F j k = F.oldest j (segE F j i) := by
    intro i
    by_cases h : r ≤ i.val
    · obtain ⟨k, hk⟩ := hsurj _ (oldest_spec hV j i h).1
      exact ⟨k, fun _ => hk⟩
    · exact ⟨i, fun h' => absurd h' h⟩
  choose g hg using hex
  refine ⟨g, ?_⟩
  intro i hi
  have hk := hg i hi
  obtain ⟨-, hev, hlt, hc⟩ := oldest_spec hV j i hi
  refine ⟨hk, hmono.lt_iff_lt.1 (by rw [hk]; exact hlt), by simp [segLL, LZ, hk, hev], ?_⟩
  rw [← hk] at hc
  refine Eq.trans ?_ hc
  have hset : (F.letters j).filter (fun z => segE F j (g i) ≤ z ∧ z < segE F j i ∧ Even z) =
      (Finset.univ.filter fun l : Fin (segN F j) => g i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).map
        ⟨segE F j, hmono.injective⟩ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hz, h1, h2, h3⟩
      obtain ⟨l, rfl⟩ := hsurj z hz
      exact ⟨l, ⟨hmono.le_iff_le.1 h1, hmono.lt_iff_lt.1 h2, by simp [segLL, LZ, h3]⟩, rfl⟩
    · rintro ⟨l, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨hmem l, hmono.le_iff_le.2 h1, hmono.lt_iff_lt.2 h2, by simpa [segLL, LZ] using h3⟩
  rw [hset, Finset.card_map]

end Formalism.MainNotions.SelectionLemmas.Pf.TE
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Num61

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

private theorem fr_lt_fr_of_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hi')
    · subst h
      exact hV.2.2.1 j i hi'

private theorem fr_le_fr_of_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ)
    (hi : i < r) : F.fr j 0 ≤ F.fr j i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact (fr_lt_fr_of_lt hV j 0 i h hi).le

private theorem fr_le_fr_last {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ)
    (hi : i < r) : F.fr j i ≤ F.fr j (r - 1) := by
  rcases Nat.lt_or_ge i (r - 1) with h | h
  · exact (fr_lt_fr_of_lt hV j i (r - 1) h (by omega)).le
  · rw [show i = r - 1 by omega]

private theorem fr_one_zero_mem_letters_one {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) :
    F.fr 1 0 ∈ F.letters 1 := by
  have hg : F.fr 0 (r - 1) < F.fr 1 0 := by
    have h0 := hV.2.2.2.1 0
    simpa using h0
  simp only [Frames.letters, sub_self, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, fr_le_fr_of_le hV 1 (r - 1) (by omega)⟩, (hV.2.2.2.2.1 1 0 (by omega)).1⟩
  have h1 := fr_le_fr_of_le hV 0 (r - 1) (by omega)
  omega

theorem six_le_Ns (hX : X.Hyp p K) : 6 ≤ X.Ns := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hg : X.F.fr 0 (r - 1) < X.F.fr 1 0 := by
    have h0 := hV.2.2.2.1 0
    simpa using h0
  have hle : ∀ j : ℤ, ∀ i, i < r → X.F.fr j 0 ≤ X.F.fr j i := fun j i hi => fr_le_fr_of_le hV j i hi
  have hleT : ∀ j : ℤ, ∀ i, i < r → X.F.fr j i ≤ X.F.fr j (r - 1) := fun j i hi => fr_le_fr_last hV j i hi
  have hinj : ∀ j : ℤ, Set.InjOn (fun i => X.F.fr j i) (Finset.range r) := by
    intro j a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    rcases lt_trichotomy a b with h | h | h
    · have h2 := fr_lt_fr_of_lt hV j a b h hb
      omega
    · exact h
    · have h2 := fr_lt_fr_of_lt hV j b a h ha
      omega
  have hAc : ((Finset.range r).image (fun i => X.F.fr 0 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 0), Finset.card_range]
  have hCc : ((Finset.range r).image (fun i => X.F.fr 1 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 1), Finset.card_range]
  have hBc : r ≤ (X.F.LLset 1).card := (hV.2.2.2.2.2.2.1 1).1
  have hsub : (Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1 ∪
      (Finset.range r).image (fun i => X.F.fr 1 i) ⊆ X.F.letters 1 := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    simp only [Frames.letters, sub_self, Finset.mem_filter, Finset.mem_Icc]
    rcases hx with (⟨i, hi, rfl⟩ | hB) | ⟨i, hi, rfl⟩
    · refine ⟨⟨hle 0 i hi, ?_⟩, (hV.2.2.2.2.1 0 i hi).1⟩
      have h1 := hleT 0 i hi
      have h2 := hle 1 (r - 1) (by omega)
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hB
      refine ⟨⟨?_, ?_⟩, hB.2⟩
      · have h1 := hle 0 (r - 1) (by omega)
        omega
      · have h1 := hle 1 (r - 1) (by omega)
        omega
    · refine ⟨⟨?_, hleT 1 i hi⟩, (hV.2.2.2.2.1 1 i hi).1⟩
      have h1 := hle 0 (r - 1) (by omega)
      have h2 := hle 1 i hi
      omega
  have hdAB : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i)) (X.F.LLset 1) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA
    obtain ⟨i, hi, rfl⟩ := hxA
    simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
    have h1 := hleT 0 i hi
    omega
  have hdABC : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1)
      ((Finset.range r).image (fun i => X.F.fr 1 i)) := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    simp only [Finset.mem_image, Finset.mem_range] at hxC
    obtain ⟨i, hi, rfl⟩ := hxC
    have h1 := hle 1 i hi
    rcases Finset.mem_union.mp hx with hxA | hxB
    · simp only [Finset.mem_image, Finset.mem_range] at hxA
      obtain ⟨i', hi', he⟩ := hxA
      have h2 := hleT 0 i' hi'
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdABC, Finset.card_union_of_disjoint hdAB, hAc, hCc] at hcard
  have h3 := hX.card 1
  omega

theorem a_big (hX : X.Hyp p K) : 416 * (X.Ns : ℝ) ≤ X.a := by
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hY := hX.Y1
  have hk : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h0 := hX.r2
    exact_mod_cast (by omega : 1 ≤ r + K)
  have hmem := fr_one_zero_mem_letters_one hX.valid (by have := hX.r2; omega)
  have hQ : 1 ≤ X.Q := (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)).trans (hX.twist 1 _ hmem)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    have h1 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
    linarith
  calc 416 * (X.Ns : ℝ) = 32 * 13 * 1 * 1 ^ 2 * X.Ns * 1 ^ 2 * 1 := by ring
    _ ≤ 32 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      gcongr
    _ ≤ X.a := hX.P3

theorem four_hundred_sixteen_le_a (hX : X.Hyp p K) : 416 ≤ X.a := by
  have h1 := a_big hX
  have h2 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  linarith

theorem log_a_ge (hX : X.Hyp p K) : 1 ≤ Real.log X.a := by
  have h := four_hundred_sixteen_le_a hX
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h2 := Real.exp_one_lt_d9
  linarith

theorem k_big (hX : X.Hyp p K) (hk : 1088 ≤ X.Ck) : 1088 * (X.Ns : ℝ) ^ 2 ≤ ((r + K : ℕ) : ℝ) := by
  have hl := log_a_ge hX
  have hP1 := hX.P1
  have hN : (0 : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ X.Ck := by linarith
  have h1 : 0 ≤ X.Ck * (X.Ns : ℝ) ^ 2 := mul_nonneg hC hN
  nlinarith [mul_le_mul_of_nonneg_left hl h1, mul_le_mul_of_nonneg_right hk hN]

theorem c_bounds (hX : X.Hyp p K) (h41 : ∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ))
    (j y : ℤ) (hy : y ∈ X.F.letters j) :
    (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
        (X.a' p K (posOf n' y) : ℝ) ∧
      (9 / 10 : ℝ) * X.a ≤ (X.a' p K (posOf n' y) : ℝ) ∧ (X.a' p K (posOf n' y) : ℝ) ≤ 2 * X.a := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hp1 : (1 : ℝ) ≤ p := by have := hX.p13; exact_mod_cast (by omega : 1 ≤ p)
  have hyL := hy
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨hy1, hy2⟩, hyT⟩ := hy
  have hdeg := hX.degs _ hyT
  have h41y := h41 _ hyT
  have ha'le : (X.a' p K (posOf n' y) : ℝ) ≤ X.deg (posOf n' y) := by
    have h0 : X.a' p K (posOf n' y) ≤ X.deg (posOf n' y) := by
      unfold Dat.a' Dat.d
      rw [if_pos hyT]
      omega
    exact_mod_cast h0
  refine ⟨?_, by linarith [hdeg.1], by linarith [hdeg.2]⟩
  have hwL : X.F.fr (j - 1) 0 ∈ X.F.letters j := by
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_refl _, ?_⟩, (hV.2.2.2.2.1 (j - 1) 0 (by omega)).1⟩
    have hg := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at hg
    have h1 := fr_le_fr_of_le hV (j - 1) (r - 1) (by omega)
    have h2 := fr_le_fr_of_le hV j (r - 1) (by omega)
    omega
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by omega)
  have hQ0 : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q := hX.twist j _ hwL
  have hQ1 : 1 ≤ X.Q := (one_le_pow₀ hp1).trans hQ0
  have hY := hX.Y1
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hk1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + K)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    have h1 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
    linarith
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  set D0 := X.F.dist j (X.F.fr (j - 1) 0) with hD0
  set Dn := 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ D0 with hDnd
  have hYk : 0 ≤ X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hDn : 0 < Dn := by
    rw [hDnd, hkdef]
    have h1 : (0 : ℝ) < (p : ℝ) ^ D0 := pow_pos (by linarith) _
    have h2 : (0 : ℝ) < X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns := by
      have h3 : (0 : ℝ) < ((r + K : ℕ) : ℝ) ^ 2 := by positivity
      have h4 : (0 : ℝ) < X.Ns := by linarith
      have h5 : (0 : ℝ) < X.Y := by linarith
      positivity
    nlinarith
  have hDa : Dn ≤ X.a := by
    have h1 : (8 : ℝ) ≤ 32 * p := by linarith
    have h2 : (p : ℝ) ^ D0 ≤ X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg X.Q)]
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by linarith)) hYk
    calc Dn = 8 * (p : ℝ) ^ D0 * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := by rw [hDnd, hkdef]; ring
      _ ≤ 32 * p * (X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1)) * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := h3
      _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 *
          ((X.E₀ : ℝ) + X.mStar + 1) := by ring
      _ ≤ X.a := hX.P3
  have hfl1 : ⌊X.a / Dn⌋₊ ≠ 0 := by
    have h1 : 1 ≤ ⌊X.a / Dn⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hDn]; linarith)
    omega
  have hRjdef : X.Rj p K j = Nat.log p ⌊X.a / Dn⌋₊ := rfl
  have hRj : (p : ℝ) ^ (X.Rj p K j) ≤ X.a / Dn := by
    have h1 : p ^ (X.Rj p K j) ≤ ⌊X.a / Dn⌋₊ := by rw [hRjdef]; exact Nat.pow_log_le_self p hfl1
    calc (p : ℝ) ^ (X.Rj p K j) = ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊X.a / Dn⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ X.a / Dn := Nat.floor_le (div_nonneg (by linarith) hDn.le)
  have hpd : (p : ℝ) ^ (X.F.dist j y) ≤ (p : ℝ) ^ D0 := pow_le_pow_right₀ hp1 hdist
  have hA : 0 ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    rw [hkdef]
    have := hYk
    nlinarith
  have e : (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
      (9 / 10) * X.a := by
    rw [pow_add]
    calc (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
        ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D0 * (X.a / Dn)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpd hRj (by positivity) (by positivity)) hA
      _ = (9 / 10) * X.a := by
          have hk0 : Dat.k (r := r) K ≠ 0 := by rw [hkdef]; linarith
          have hY0 : X.Y ≠ 0 := by linarith
          have hN0 : (X.Ns : ℝ) ≠ 0 := by linarith
          have hpD : (p : ℝ) ^ D0 ≠ 0 := pow_ne_zero _ (by linarith)
          rw [hDnd]
          field_simp
          ring
  linarith [hdeg.1, h41y]

theorem Bdeg_bounds (hX : X.Hyp p K) (hk : 1088 ≤ X.Ck)
    (h41 : ∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ))
    (j : ℤ) (b : ℤ → ℕ) (hA : X.AdmLL p K j b) (x : ℤ) (hx : x ∈ X.F.letters j) (hlt : x < X.F.fr j 0) :
    (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) - 2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) x : ℝ) ∧
      (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hpp : 0 < p ^ (X.F.dist j x + X.Rj p K j) := pow_pos hX.prime.pos _
  have hPc : ((p ^ (X.F.dist j x + X.Rj p K j) : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    push_cast
    ring
  have hP0 : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by rw [← hPc]; exact_mod_cast hpp
  unfold Dat.Bdeg
  by_cases hW : X.F.IsW j x
  · rw [if_pos hW]
    unfold Dat.Bw Dat.m0
    set A := X.a' p K (posOf n' x) with hAdef
    set pp := p ^ (X.F.dist j x + X.Rj p K j) with hppdef
    have hq1 : ((A / pp : ℕ) : ℝ) ≤ (A : ℝ) / (pp : ℝ) := Nat.cast_div_le
    have hq2 : (A : ℝ) / (pp : ℝ) < ((A / pp : ℕ) : ℝ) + 1 := by
      have hmod := Nat.div_add_mod A pp
      have hlt := Nat.mod_lt A hpp
      have hppR : (0 : ℝ) < (pp : ℝ) := by exact_mod_cast hpp
      rw [div_lt_iff₀ hppR]
      have e1 : (A : ℝ) = (pp : ℝ) * ((A / pp : ℕ) : ℝ) + ((A % pp : ℕ) : ℝ) := by exact_mod_cast hmod.symm
      have e2 : ((A % pp : ℕ) : ℝ) < (pp : ℝ) := by exact_mod_cast hlt
      nlinarith
    rw [← hPc]
    set z : ℤ := ((A / pp : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ) - (((r + K) * X.Ns + 1 : ℕ) : ℤ) with hz
    have hzR : (z : ℝ) = ((A / pp : ℕ) : ℝ) - ((r + K + r + 1 : ℕ) : ℝ) - (((r + K) * X.Ns + 1 : ℕ) : ℝ) := by
      simp only [hz, Int.cast_sub, Int.cast_natCast]
    have hc1 : ((r + K + r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + K + 1 := by push_cast; ring
    have hc2 : (((r + K) * X.Ns + 1 : ℕ) : ℝ) = ((r : ℝ) + K) * X.Ns + 1 := by push_cast; ring
    rw [hc1, hc2] at hzR
    have hzt1 : (z : ℝ) ≤ ((z.toNat : ℕ) : ℝ) := by
      have h1 : z ≤ (z.toNat : ℤ) := Int.self_le_toNat z
      exact_mod_cast h1
    have hzt2 : ((z.toNat : ℕ) : ℝ) ≤ max (z : ℝ) 0 := by
      rcases le_or_gt 0 z with h | h
      · have h1 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have h2 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast h1
        rw [h2]
        exact le_max_left _ _
      · rw [Int.toNat_of_nonpos h.le]
        simp
    have hApos : (0 : ℝ) ≤ (A : ℝ) / (pp : ℝ) := by positivity
    have hkc : ((r + K : ℕ) : ℝ) = (r : ℝ) + K := by push_cast; ring
    rw [hkdef, hkc]
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hprod : ((r : ℝ) + K) * 6 ≤ ((r : ℝ) + K) * X.Ns :=
      mul_le_mul_of_nonneg_left hNs (by linarith)
    constructor
    · linarith
    · have h1 : max (z : ℝ) 0 ≤ (A : ℝ) / (pp : ℝ) := by
        apply max_le
        · rw [hzR]
          have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
          have h3 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ ((r : ℝ) + K) * X.Ns := by positivity
          linarith
        · exact hApos
      linarith
  · rw [if_neg hW]
    have hxl := hx
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hxl
    have hlate : x ∈ X.toLate j := by
      unfold Dat.toLate
      simp only [Finset.mem_filter]
      exact ⟨hx, hW⟩
    unfold Dat.restr
    rw [if_pos hlate]
    have hLL : x ∈ X.F.LLset j := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      unfold Frames.IsW at hW
      push_neg at hW
      exact ⟨⟨hW, hlt⟩, hxl.2⟩
    obtain ⟨h1, h2⟩ := hA x hLL
    have hPz : ((X.Pz p K j x : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
      unfold Dat.Pz
      push_cast
      ring
    rw [hPz] at h1 h2
    rw [hkdef] at h1 ⊢
    have h3 : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((r + K : ℕ) : ℝ) ≤ 2 * ((r + K : ℕ) : ℝ) * (X.Ns : ℝ) := by nlinarith
    constructor
    · linarith
    · exact h2

end Num61

end Formalism.MainNotions.SelectionLemmas.Pf.TE
