module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Cells

section Comb
variable {F : Type} [Field F]

def Good (k : ℕ) (d : ℕ → F) : Prop := d 0 ≠ 0 ∧ ∀ a, k ≤ a → d a = 1

def st (d : ℕ → F) (b : ℕ) : ℕ := Nat.findGreatest (fun a => d a ≠ 0) b

def en (d : ℕ → F) (b : ℕ) : ℕ := sInf {a | b < a ∧ d a ≠ 0}

def sg (k : ℕ) (d : ℕ → F) (b : ℕ) : ℕ := if b < k then k - en d b + (b - st d b) else b

lemma st_le (d : ℕ → F) (b : ℕ) : st d b ≤ b := Nat.findGreatest_le b

lemma st_ne {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : d (st d b) ≠ 0 :=
  Nat.findGreatest_spec (P := fun a => d a ≠ 0) (Nat.zero_le b) h.1

lemma le_st {d : ℕ → F} {a b : ℕ} (hab : a ≤ b) (ha : d a ≠ 0) : a ≤ st d b :=
  Nat.le_findGreatest (P := fun a => d a ≠ 0) hab ha

lemma en_spec {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : b < en d b ∧ d (en d b) ≠ 0 := by
  have : ({a | b < a ∧ d a ≠ 0} : Set ℕ).Nonempty :=
    ⟨b + k + 1, by omega, by rw [h.2 _ (by omega)]; exact one_ne_zero⟩
  exact Nat.sInf_mem this

lemma en_le {d : ℕ → F} {a b : ℕ} (hab : b < a) (ha : d a ≠ 0) : en d b ≤ a :=
  Nat.sInf_le (show a ∈ {a | b < a ∧ d a ≠ 0} from ⟨hab, ha⟩)

lemma en_le_k {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : en d b ≤ k :=
  en_le hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)

lemma dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) :
    (st d c = st d b ∧ en d c = en d b) ∨ en d c ≤ st d b := by
  by_cases h1 : en d c ≤ b
  · exact Or.inr (le_st h1 (en_spec h c).2)
  · left
    have h2 := en_le (d := d) (b := c) (a := en d b) (by have := (en_spec h b).1; omega) (en_spec h b).2
    have h3 := en_le (d := d) (b := b) (a := en d c) (by omega) (en_spec h c).2
    have h4 := le_st (d := d) (a := st d c) (b := b) (by have := st_le d c; omega) (st_ne h c)
    refine ⟨?_, by omega⟩
    by_cases h5 : st d b ≤ c
    · have := le_st h5 (st_ne h b); omega
    · have := en_le (d := d) (b := c) (a := st d b) (by omega) (st_ne h b)
      have := st_le d b; omega

lemma sg_lt {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : sg k d b < k := by
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  simp only [sg, if_pos hb]; omega

lemma sg_ge {k : ℕ} (d : ℕ → F) {b : ℕ} (hb : k ≤ b) : sg k d b = b := by
  simp only [sg, if_neg (not_lt.2 hb)]

lemma sg_dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) (hb : b < k) :
    (st d c = st d b ∧ sg k d c + b = sg k d b + c) ∨ (c < st d b ∧ sg k d b < sg k d c) := by
  have hc : c < k := by omega
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  have := en_spec h c; have := en_le_k h hc; have := st_le d c
  simp only [sg, if_pos hb, if_pos hc]
  rcases dich h hcb with h1 | h1 <;> omega

lemma sg_inj {k : ℕ} {d : ℕ → F} (h : Good k d) : Function.Injective (sg k d) := by
  intro c b hcb
  wlog hlt : c < b generalizing c b
  · rcases Nat.lt_or_ge b c with h1 | h1
    · exact (this hcb.symm h1).symm
    · omega
  by_cases hb : b < k
  · have := sg_dich h hlt hb; omega
  · rw [sg_ge d (not_lt.1 hb)] at hcb
    by_cases hc : c < k
    · have := sg_lt h hc; omega
    · rwa [sg_ge d (not_lt.1 hc)] at hcb

lemma st_ge {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : k ≤ b) : d (st d b) = 1 := by
  have := le_st (d := d) hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)
  exact h.2 _ this

lemma st_eq_iff {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : st d b = b ↔ d b ≠ 0 := by
  constructor
  · intro h1; have := st_ne h b; rwa [h1] at this
  · intro h1; exact le_antisymm (st_le d b) (le_st le_rfl h1)

lemma ext_of {k : ℕ} {d d' : ℕ → F} (h : Good k d) (h' : Good k d')
    (H : ∀ b < k, sg k d b = sg k d' b ∧ d (st d b) = d' (st d' b)) : d = d' := by
  funext b
  by_cases hb : b < k
  swap
  · rw [h.2 b (not_lt.1 hb), h'.2 b (not_lt.1 hb)]
  have key : st d b = b ↔ st d' b = b := by
    have := st_le d b; have := st_le d' b
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · omega
    · have := sg_dich h (c := b - 1) (b := b) (by omega) hb
      have := sg_dich h' (c := b - 1) (b := b) (by omega) hb
      have := (H b hb).1
      have := (H (b - 1) (by omega)).1
      have := st_le d (b - 1); have := st_le d' (b - 1)
      omega
  by_cases h1 : st d b = b
  · have := (H b hb).2
    rwa [h1, key.1 h1] at this
  · have h2 : ¬ st d' b = b := fun h2 => h1 (key.2 h2)
    rw [st_eq_iff h, not_not] at h1
    rw [st_eq_iff h', not_not] at h2
    rw [h1, h2]

def mono {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) : GL (Fin N) F where
  val := Matrix.of fun a b => if a = σ b then t b else 0
  inv := Matrix.of fun a b => if b = σ a then (t a)⁻¹ else 0
  val_inv := by
    ext a b
    obtain ⟨c, rfl⟩ := σ.surjective a
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · by_cases h : σ c = b
      · subst h; simp [ht]
      · simp [h, Ne.symm h]
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · by_cases h : a = b
      · subst h; simp [ht]
      · simp [h]
    · intro x _ hx; simp [hx]
    · simp

lemma mono_val {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (a b : Fin N) :
    (mono σ t ht).val a b = if a = σ b then t b else 0 := rfl

lemma mono_rel {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (u u' : GL (Fin N) F)
    (h : u * mono σ t ht = mono σ t ht * u') (c b : Fin N) : u.val (σ c) (σ b) * t b = t c * u'.val c b := by
  have := congrArg (fun x : GL (Fin N) F => x.val (σ c) b) h
  simpa [Units.val_mul, Matrix.mul_apply, mono_val] using this

def perm {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun b => ⟨sg k d b, by
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb; omega
      · rw [sg_ge d (not_lt.1 hb)]; exact b.2⟩)
    (Finite.injective_iff_bijective.1 fun a b hab => Fin.ext (sg_inj h (congrArg Fin.val hab)))

lemma perm_val {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) (b : Fin N) : (perm hk h b : ℕ) = sg k d b := rfl

def cell {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : GL (Fin N) F :=
  mono (perm hk h) (fun b => d (st d b)) fun b => st_ne h b

def dat (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) (a : ℕ) : F :=
  if k ≤ a then 1 else if a = 0 then (p.1 : F) else if h : a - 1 < k - 1 then p.2 ⟨a - 1, h⟩ else 1

lemma dat_good (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) : Good k (dat k p) := by
  refine ⟨?_, fun a ha => by simp [dat, ha]⟩
  unfold dat
  split_ifs <;> simp_all

lemma dat_inj {k : ℕ} (hk : 0 < k) : Function.Injective (dat (F := F) k) := by
  intro p q h
  ext i
  · have := congrFun h 0
    simpa [dat, hk.ne'] using this
  · have := congrFun h (i + 1)
    have hi := i.2
    have h1 : ¬ k ≤ i + 1 := by omega
    simpa [dat, h1] using this

lemma cell_inj {k N : ℕ} (hk : k < N) {d d' : ℕ → F} (h : Good k d) (h' : Good k d') (H : cell hk h = cell hk h') :
    d = d' := by
  refine ext_of h h' fun b hb => ?_
  have h1 := congrArg (fun x : GL (Fin N) F => x.val (perm hk h ⟨b, by omega⟩) ⟨b, by omega⟩) H
  simp only [cell, mono_val, if_true] at h1
  split_ifs at h1 with h2
  · exact ⟨congrArg Fin.val h2, h1⟩
  · exact absurd h1 (st_ne h b)

end Comb

theorem relevant_cells : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  intro g _ N L hs hco k hk0 hk
  refine ⟨Finset.univ.image fun p : (ZMod g)ˣ × (Fin (k - 1) → ZMod g) => cell hk (dat_good k p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ fun p q h => dat_inj hk0 (cell_inj hk _ _ h)]
    simp [Nat.totient_prime (Fact.out : g.Prime)]
  · intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    refine ⟨fun a b hab => ?_, perm hk h, fun a b hab => ?_⟩
    · simp only [cell, mono_val, Fin.ext_iff, perm_val]
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [sg_ge _ (not_lt.1 hb), st_ge h (not_lt.1 hb)]
    · by_contra h1
      exact hab (by simp only [cell, mono_val]; exact if_neg h1)
  · intro w hw u u' hu hu' hb hb' H
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    set d := dat k p
    have rel := mono_rel _ _ _ u u' H
    unfold Lev.chi
    congr 1
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have r := rel c b
    simp only [Lev.Edge, hs, hco, Units.val_one, one_mul, Bool.false_eq_true, if_false, perm_val]
    have tb := st_ne h b
    have tc := st_ne h c
    have hσ : ∀ x : Fin N, (x : ℕ) < k → sg k d x < k := fun x hx => sg_lt h hx
    have hσ' : ∀ x : Fin N, k ≤ (x : ℕ) → sg k d x = x := fun x hx => sg_ge d hx
    have z : c ≠ b → (k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c) →
        u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := by
      intro hne hh
      have e1 : u'.val c b = 0 → u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := fun e =>
        ⟨by rw [e, mul_zero] at r; exact (mul_eq_zero.1 r).resolve_right tb, e⟩
      rcases hh with hh | hh | hh
      · exact e1 (by rw [hb' c b (Or.inr hh), if_neg hne])
      · exact e1 (hu'.2 _ _ hh)
      · have e : u.val (perm hk h c) (perm hk h b) = 0 := hu.2 _ _ hh
        exact ⟨e, by rw [e, zero_mul] at r; exact (mul_eq_zero.1 r.symm).resolve_left tc⟩
    by_cases hne : c = b
    · subst hne; simp
    by_cases hh : k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c
    · obtain ⟨z1, z2⟩ := z hne hh
      simp [z1, z2]
    · have hne' : (c : ℕ) ≠ b := fun e => hne (Fin.ext e)
      simp only [not_or, Fin.lt_def] at hh
      rcases sg_dich h (c := c) (b := b) (by omega) (by omega) with ⟨e1, e2⟩ | e
      · have e3 : u.val (perm hk h c) (perm hk h b) = u'.val c b := by
          rw [e1, mul_comm] at r
          exact mul_left_cancel₀ tb r
        rw [e3]
        exact if_congr (by omega) rfl rfl
      · omega

end GlobalTheory.BadShare.Cells
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatumStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  first | exact @GlobalTheory.BadShare.Cells.relevant_cells | exact GlobalTheory.BadShare.Cells.relevant_cells | (intros; apply GlobalTheory.BadShare.Cells.relevant_cells <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependent
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Indep

lemma inv_of_mul_closed {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1)
    (hm : ∀ a b, S a → S b → S (a * b)) (a : G) (ha : S a) : S a⁻¹ := by
  have hp : ∀ n : ℕ, S (a ^ n) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm _ _ ih ha
  have hpos : 0 < orderOf a := orderOf_pos a
  have : a⁻¹ = a ^ (orderOf a - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [this]; exact hp _

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def RowUp (k : ℕ) (h : GG g N) : Prop :=
  ∀ a : Fin N, k ≤ (a : ℕ) → h.val a a = 1 ∧ ∀ b, b < a → h.val a b = 0

def Corner (k : ℕ) (h : GG g N) : Prop :=
  ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → h.val a b = if a = b then 1 else 0

lemma rowUp_one (k : ℕ) : RowUp k (1 : GG g N) := by
  intro a _
  refine ⟨by simp, fun b hb => ?_⟩
  simp [Matrix.one_apply, hb.ne']

lemma rowUp_mul (k : ℕ) (h h' : GG g N) (H : RowUp k h) (H' : RowUp k h') : RowUp k (h * h') := by
  have key : ∀ a b : Fin N, k ≤ (a : ℕ) → b ≤ a → (h * h').val a b = h'.val a b := by
    intro a b ha hb
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(H a ha).1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [(H a ha).2 c hc, zero_mul]
      · rw [(H' c (le_trans ha (le_of_lt hc))).2 b (lt_of_le_of_lt hb hc), mul_zero]
    · simp
  intro a ha
  refine ⟨by rw [key a a ha le_rfl, (H' a ha).1], fun b hb => ?_⟩
  rw [key a b ha hb.le, (H' a ha).2 b hb]

lemma rowUp_inv (k : ℕ) (h : GG g N) (H : RowUp k h) : RowUp k h⁻¹ :=
  inv_of_mul_closed (RowUp k) (rowUp_one k) (rowUp_mul k) h H

lemma corner_one (k : ℕ) : Corner k (1 : GG g N) := by
  intro a b _
  simp [Matrix.one_apply]

lemma corner_mul (k : ℕ) (h h' : GG g N) (H : Corner k h) (H' : Corner k h') : Corner k (h * h') := by
  intro a b hab
  rw [Units.val_mul, Matrix.mul_apply]
  rcases hab with ha | hb
  · rw [Finset.sum_eq_single a]
    · rw [H a a (Or.inl ha), H' a b (Or.inl ha)]; simp
    · intro c _ hc
      rw [H a c (Or.inl ha)]; simp [hc.symm]
    · simp
  · rw [Finset.sum_eq_single b]
    · rw [H a b (Or.inr hb), H' b b (Or.inr hb)]; simp
    · intro c _ hc
      rw [H' c b (Or.inr hb)]; simp [hc]
    · simp

lemma corner_inv (k : ℕ) (h : GG g N) (H : Corner k h) : Corner k h⁻¹ :=
  inv_of_mul_closed (Corner k) (corner_one k) (corner_mul k) h H

lemma Corner.rowUp {k : ℕ} {h : GG g N} (H : Corner k h) : RowUp k h := by
  intro a ha
  refine ⟨by rw [H a a (Or.inl ha)]; simp, fun b hb => ?_⟩
  rw [H a b (Or.inl ha)]; simp [hb.ne']

lemma rowUp_zero_iff (h : GG g N) : RowUp 0 h ↔ IsUp g N h :=
  ⟨fun H => ⟨fun a => (H a (Nat.zero_le _)).1, fun a b hb => (H a (Nat.zero_le _)).2 b hb⟩,
    fun H a _ => ⟨H.1 a, fun b hb => H.2 a b hb⟩⟩

def colElt (n : Fin N) (w : Fin N → ZMod g) (hw : w n = 0) : GG g N where
  val := 1 + Matrix.vecMulVec w (Pi.single n 1)
  inv := 1 - Matrix.vecMulVec w (Pi.single n 1)
  val_inv := by
    have : Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) * Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec]; simp [hw]
    rw [add_mul, mul_sub, mul_sub, this]; simp
  inv_val := by
    have : Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) * Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec]; simp [hw]
    rw [sub_mul, mul_add, mul_add, this]; simp

lemma conj_colElt (n : Fin N) (w : Fin N → ZMod g) (hw : w n = 0) (h : GG g N) (a b : Fin N) :
    (h⁻¹ * colElt n w hw * h).val a b =
      (if a = b then 1 else 0) + (∑ c, (h⁻¹).val a c * w c) * h.val n b := by
  have e : (h⁻¹ * colElt n w hw * h).val =
      1 + (h⁻¹).val * Matrix.vecMulVec w (Pi.single n 1) * h.val := by
    rw [Units.val_mul, Units.val_mul]
    show (h⁻¹).val * (1 + Matrix.vecMulVec w (Pi.single n 1)) * h.val = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul]
  rw [e, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  simp [Matrix.mulVec, dotProduct]

lemma act_colElt {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (m n : Fin N) (hmn : (n : ℕ) = m + 1)
    (w : Fin N → ZMod g) (hw : ∀ c, n ≤ c → w c = 0) (h : GG g N) (H : RowUp n h) :
    ρ (colElt n w (hw n le_rfl)) (ρ h x) = L.ψ ((L.co m : ZMod g) * ∑ c, (h⁻¹).val m c * w c) • ρ h x := by
  have Hi := rowUp_inv _ _ H
  have hz : ∀ a : Fin N, n ≤ a → ∑ c, (h⁻¹).val a c * w c = 0 := by
    intro a ha
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c n with hc | hc
    · rw [(Hi a ha).2 c (lt_of_lt_of_le hc ha), zero_mul]
    · rw [hw c hc, mul_zero]
  have hn := H n le_rfl
  have hle : ∀ a b : Fin N, b ≤ a → (∑ c, (h⁻¹).val a c * w c) * h.val n b = 0 := by
    intro a b hb
    rcases lt_or_ge a n with hc | hc
    · rw [hn.2 b (lt_of_le_of_lt hb hc), mul_zero]
    · rw [hz a hc, zero_mul]
  set u := h⁻¹ * colElt n w (hw n le_rfl) * h with hu
  have hup : IsUp g N u := by
    refine ⟨fun a => ?_, fun a b hb => ?_⟩
    · rw [hu, conj_colElt, hle a a le_rfl]; simp
    · rw [hu, conj_colElt, hle a b hb.le]; simp [hb.ne']
  have hchi : L.chi u = L.ψ ((L.co m : ZMod g) * ∑ c, (h⁻¹).val m c * w c) := by
    unfold Lev.chi
    congr 1
    have hE : ∀ a b : Fin N, L.Edge a b ↔ (b : ℕ) = a + 1 := by
      intro a b; simp [Lev.Edge, hL]
    rw [Finset.sum_eq_single m, Finset.sum_eq_single n]
    · rw [if_pos ((hE m n).2 hmn), hu, conj_colElt, hn.1, if_neg (by intro e; rw [e] at hmn; omega)]
      simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext (by rw [(hE m b).1 e, hmn]))
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with e
      · have e' := (hE a b).1 e
        rw [hu, conj_colElt, if_neg (by intro e; rw [e] at e'; omega), zero_add]
        have ha' : (a : ℕ) ≠ m := fun e => ha (Fin.ext e)
        rcases lt_or_ge a n with hc | hc
        · rw [hn.2 b (by rw [Fin.lt_def] at hc ⊢; omega)]; simp
        · rw [hz a hc]; simp
      · rfl
    · simp
  have e : colElt n w (hw n le_rfl) * h = h * u := by rw [hu]; group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx u hup, map_smul, hchi]

lemma sum_char (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (d : Fin N → ZMod g) (hd : d ≠ 0) :
    ∑ v : Fin N → ZMod g, ψ (∑ c, d c * v c) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hd
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.1 hψ
  have hc' : d c ≠ 0 := hc
  have ht' : ψ t ≠ 1 := by simpa using ht
  have e := Equiv.sum_comp (Equiv.addRight (Pi.single c (t / d c) : Fin N → ZMod g))
    (fun v : Fin N → ZMod g => ψ (∑ c, d c * v c))
  have e2 : ∀ v : Fin N → ZMod g, ψ (∑ c', d c' * (Equiv.addRight (Pi.single c (t / d c) : Fin N → ZMod g) v) c') =
      ψ t * ψ (∑ c, d c * v c) := by
    intro v
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Equiv.coe_addRight, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single c]
    · simp; field_simp
    · intro b _ hb; simp [hb]
    · simp
  simp only [e2, ← Finset.mul_sum] at e
  have : (ψ t - 1) * ∑ v : Fin N → ZMod g, ψ (∑ c, d c * v c) = 0 := by rw [sub_mul, e]; simp
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht')

lemma step {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (k : ℕ) (hk : k + 1 < N)
    (φ : GG g N → ℂ) (hφ : ∀ h, φ h ≠ 0 → RowUp (k + 1) h) (hs : ∑ h, φ h • ρ h x = 0) :
    ∑ h, (if RowUp k h then φ h else 0) • ρ h x = 0 := by
  let m : Fin N := ⟨k, by omega⟩
  let n : Fin N := ⟨k + 1, hk⟩
  let tr : (Fin N → ZMod g) → Fin N → ZMod g := fun v c => if c < n then v c else 0
  have htr : ∀ v c, n ≤ c → tr v c = 0 := fun v c hc => if_neg (not_lt.2 hc)
  let d : GG g N → Fin N → ZMod g := fun h c =>
    if c < n then (L.co m : ZMod g) * ((h⁻¹).val m c - if m = c then 1 else 0) else 0
  have hmn : m < n := by simp [m, n, Fin.lt_def]
  have h1 : ∀ (v : Fin N → ZMod g) (h : GG g N),
      L.ψ (-((L.co m : ZMod g) * v m)) • ρ (colElt n (tr v) (htr v n le_rfl)) (φ h • ρ h x) =
        L.ψ (∑ c, d h c * v c) • φ h • ρ h x := by
    intro v h
    by_cases h0 : φ h = 0
    · simp [h0]
    rw [map_smul, act_colElt ρ L hL x hx m n rfl (tr v) (htr v) h (hφ h h0), smul_comm (φ h), smul_smul,
      ← AddChar.map_add_eq_mul]
    congr 2
    have : v m = ∑ c, (if m = c then 1 else 0) * tr v c := by
      rw [Finset.sum_eq_single m]
      · simp [tr, hmn]
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [this, neg_add_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [d, tr]
    split_ifs <;> ring
  have h2 : ∀ h : GG g N, (∑ v : Fin N → ZMod g, L.ψ (∑ c, d h c * v c)) • φ h • ρ h x =
      (Fintype.card (Fin N → ZMod g) : ℂ) • (if RowUp k h then φ h else 0) • ρ h x := by
    intro h
    by_cases h0 : φ h = 0
    · simp [h0]
    by_cases hR : RowUp k h
    · have Hi := rowUp_inv _ _ hR m le_rfl
      have : d h = 0 := by
        funext c
        simp only [d]
        split_ifs with a b
        · subst b; rw [Hi.1]; simp
        · rw [Hi.2 c (by
            have : (m : ℕ) ≠ c := fun e => b (Fin.ext e)
            simp only [Fin.lt_def, m, n] at a this ⊢; omega)]
          simp
        · rfl
      simp [this, hR]
    · rw [if_neg hR, sum_char L.ψ L.hψ]
      · simp
      · intro hd
        apply hR
        have Hi := rowUp_inv _ _ (hφ h h0)
        have hrow : ∀ c, c < n → (h⁻¹).val m c = if m = c then 1 else 0 := by
          intro c hc
          have := congrFun hd c
          simp only [d, if_pos hc, Pi.zero_apply] at this
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (L.co m).ne_zero)
        have : RowUp k h⁻¹ := by
          intro a ha
          rcases ha.eq_or_lt with e | e
          · have : a = m := Fin.ext e.symm
            subst this
            refine ⟨by rw [hrow _ hmn]; simp, fun b hb => ?_⟩
            rw [hrow _ (hb.trans hmn)]; simp [hb.ne']
          · exact Hi a e
        simpa using rowUp_inv _ _ this
  have h3 : ∑ v : Fin N → ZMod g,
      L.ψ (-((L.co m : ZMod g) * v m)) • ρ (colElt n (tr v) (htr v n le_rfl)) (∑ h, φ h • ρ h x) = 0 := by
    simp [hs]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum] at h3
  rw [Finset.sum_comm, Finset.sum_congr rfl fun h _ => ((Finset.sum_congr rfl fun v _ => h1 v h).trans (Finset.sum_smul.symm.trans (h2 h))), ← Finset.smul_sum] at h3
  exact (smul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

lemma sum_up {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx0 : x ≠ 0) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (k : ℕ) (hk : k < N)
    (φ : GG g N → ℂ) (hφ : ∀ h, φ h ≠ 0 → RowUp k h) (hs : ∑ h, φ h • ρ h x = 0) :
    ∑ u, (if IsUp g N u then φ u * L.chi u else 0) = 0 := by
  induction k generalizing φ with
  | zero =>
    have : ∀ h, φ h • ρ h x = (if IsUp g N h then φ h * L.chi h else 0) • x := by
      intro h
      by_cases h0 : φ h = 0
      · simp [h0]
      have := (rowUp_zero_iff h).1 (hφ h h0)
      rw [if_pos this, hx h this, smul_smul]
    simp only [this, ← Finset.sum_smul] at hs
    exact (smul_eq_zero.1 hs).resolve_right hx0
  | succ k ih =>
    have := ih (by omega) (fun h => if RowUp k h then φ h else 0)
      (fun h hh => by by_contra e; exact hh (if_neg e)) (step ρ L hL x hx k hk φ hφ hs)
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) this
    split_ifs with a b
    · rfl
    · exact absurd (fun c _ => ⟨a.1 c, fun b hb => a.2 c b hb⟩) b
    · rfl

theorem translates_independent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  intro g _ N M _ _ _ ρ L hL x hx0 hx k hk φ hφ hs h₀
  have hφ' : ∀ h, φ h ≠ 0 → Corner k h := hφ
  by_cases h0 : Corner k h₀
  · have hc : ∀ p, φ (h₀ * p) ≠ 0 → Corner k p := by
      intro p hp
      simpa using corner_mul k _ _ (corner_inv k _ h0) (hφ' _ hp)
    have hs' : ∑ p, φ (h₀ * p) • ρ p x = 0 := by
      have e := Equiv.sum_comp (Equiv.mulLeft h₀) (fun h => φ h • ρ h x)
      have e2 := congrArg (ρ h₀⁻¹) (e.trans hs)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at e2
      rw [← e2]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Equiv.coe_mulLeft, map_smul]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
    have := sum_up ρ L hL x hx0 hx k hk (fun p => φ (h₀ * p)) (fun p hp => (hc p hp).rowUp) hs'
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) this
    by_cases e : φ (h₀ * u) = 0
    · simp [e]
    have hu : ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → u.val a b = if a = b then 1 else 0 := hc u e
    by_cases e' : IsUp g N u
    · rw [if_pos ⟨e', hu⟩, if_pos e']
    · rw [if_neg (fun h => e' h.1), if_neg e']
  · refine Finset.sum_eq_zero fun u hu => ?_
    have hu' : Corner k u := (Finset.mem_filter.1 hu).2.2
    have : φ (h₀ * u) = 0 := by
      by_contra e
      apply h0
      simpa using corner_mul k _ _ (hφ' _ e) (corner_inv k _ hu')
    rw [this, zero_mul]

end GlobalTheory.BadShare.Indep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependentStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_translates_corner_linearIndependent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  first | exact @GlobalTheory.BadShare.Indep.translates_independent | exact GlobalTheory.BadShare.Indep.translates_independent | (intros; apply GlobalTheory.BadShare.Indep.translates_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.FirstRows

theorem inv_mem_of_mul_mem {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1)
    (hm : ∀ u v, S u → S v → S (u * v)) (u : G) (hu : S u) : S u⁻¹ := by
  have hp : ∀ n : ℕ, S (u ^ n) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm _ _ ih hu
  have : u⁻¹ = u ^ (orderOf u - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
  rw [this]; exact hp _

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def InBlock (k : ℕ) (h : GG g N) : Prop :=
  ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → h.val a b = if a = b then 1 else 0

theorem inBlock_one (k : ℕ) : InBlock k (1 : GG g N) := by
  intro a b _
  simp [Matrix.one_apply]

theorem InBlock.mul_right {k : ℕ} {h : GG g N} (hh : InBlock k h) (A : Matrix (Fin N) (Fin N) (ZMod g))
    (a b : Fin N) (hb : k ≤ (b : ℕ)) : (A * h.val) a b = A a b := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [hh c b (Or.inr hb)]]
  simp

theorem InBlock.mul_left {k : ℕ} {h : GG g N} (hh : InBlock k h) (A : Matrix (Fin N) (Fin N) (ZMod g))
    (a b : Fin N) (ha : k ≤ (a : ℕ)) : (h.val * A) a b = A a b := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [hh a c (Or.inl ha)]]
  simp

theorem InBlock.mul {k : ℕ} (h h' : GG g N) (hh : InBlock k h) (hh' : InBlock k h') : InBlock k (h * h') := by
  intro a b hab
  rw [Units.val_mul]
  rcases hab with ha | hb
  · rw [hh.mul_left _ _ _ ha]; exact hh' a b (Or.inl ha)
  · rw [hh'.mul_right _ _ _ hb]; exact hh a b (Or.inr hb)

theorem InBlock.inv {k : ℕ} {h : GG g N} (hh : InBlock k h) : InBlock k h⁻¹ :=
  inv_mem_of_mul_mem _ (inBlock_one k) InBlock.mul h hh

theorem conj_entry {k : ℕ} {h n : GG g N} (hh : InBlock k h)
    (hn : ∀ a b : Fin N, (b : ℕ) ≤ k → n.val a b = if a = b then 1 else 0)
    (a b : Fin N) (hab : (b : ℕ) ≤ k ∨ k ≤ (a : ℕ)) : (h⁻¹ * (n * h)).val a b = n.val a b := by
  by_cases hb : (b : ℕ) ≤ k
  · have h1 : ∀ a, (n.val * h.val) a b = h.val a b := by
      intro a
      have : ∀ c, n.val a c * h.val c b = (if a = c then 1 else 0) * h.val c b := by
        intro c
        by_cases hc : (c : ℕ) ≤ k
        · rw [hn a c hc]
        · have : c ≠ b := by rintro rfl; exact hc hb
          rw [hh c b (Or.inl (by omega)), if_neg this, mul_zero, mul_zero]
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => this c]
      simp
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [h1 c],
      ← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, hn a b hb]
    simp [Matrix.one_apply]
  · have ha : k ≤ (a : ℕ) := by omega
    rw [Units.val_mul, Units.val_mul, hh.inv.mul_left _ _ _ ha, hh.mul_right _ _ _ (by omega)]

theorem exists_block {k : ℕ} {j : GG g N} (hj : IsUp g N j)
    (hk : ∀ a b : Fin N, (a : ℕ) < k → (b : ℕ) = k → j.val a b = 0) :
    ∃ u : GG g N, IsUp g N u ∧ InBlock k u ∧
      ∀ a b : Fin N, (b : ℕ) ≤ k → (u⁻¹ * j).val a b = if a = b then 1 else 0 := by
  let A : Matrix (Fin N) (Fin N) (ZMod g) := fun a b =>
    if (a : ℕ) < k ∧ (b : ℕ) < k then j.val a b else if a = b then 1 else 0
  have hd : ∀ a, A a a = 1 := by
    intro a; simp [A, hj.1]
  have hl : ∀ a b, b < a → A a b = 0 := by
    intro a b hab; simp [A, hj.2 a b hab, hab.ne']
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun a b hab => hl a b hab)]
    simp [hd]
  let u : GG g N := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet
  have hu : u.val = A := rfl
  refine ⟨u, ⟨hd, hl⟩, ?_, ?_⟩
  · intro a b hab
    rw [hu]
    exact if_neg (by omega)
  · intro a b hb
    have h1 : ∀ c, j.val c b = u.val c b := by
      intro c
      rw [hu]
      simp only [A]
      split_ifs with h1 h2
      · rfl
      · subst h2; exact hj.1 _
      · rcases lt_or_gt_of_ne h2 with h | h
        · have : (c : ℕ) < b := h
          exact hk c b (by omega) (by omega)
        · exact hj.2 _ _ h
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [h1 c],
      ← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel]
    simp [Matrix.one_apply]

theorem mem_iff_isUp {L : Lev g N} (hL : L.sharp = false) (u : GG g N) : L.Mem u ↔ IsUp g N u := by
  simp [Lev.Mem, hL]

theorem chi_congr {L : Lev g N} (hL : L.sharp = false) {u v : GG g N}
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → u.val a b = v.val a b) : L.chi u = L.chi v := by
  unfold Lev.chi
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with he
  · rw [h a b (by simpa [Lev.Edge, hL] using he)]
  · rfl

theorem chi_ne_zero (L : Lev g N) (u : GG g N) : L.chi u ≠ 0 := by
  intro h
  unfold Lev.chi at h
  have := AddChar.map_add_eq_mul L.ψ (∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0)
    (-(∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0))
  rw [h] at this
  simp at this

def blockUp (g : ℕ) [Fact g.Prime] (N k : ℕ) : Finset (GG g N) :=
  Finset.univ.filter fun u => IsUp g N u ∧ InBlock k u

theorem mem_blockUp {k : ℕ} {u : GG g N} : u ∈ blockUp g N k ↔ IsUp g N u ∧ InBlock k u := by
  simp [blockUp]

variable {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M)

def avg (L : Lev g N) (k : ℕ) (x : M) (w : GG g N) : M :=
  ∑ u ∈ blockUp g N k, (L.chi u)⁻¹ • ρ (u * w) x

theorem avg_eigen {L : Lev g N} (hL : L.sharp = false) {x : M} (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x)
    {k : ℕ} {w : GG g N} (hw : InBlock k w) {j : GG g N} (hj : IsUp g N j)
    (hk : ∀ a b : Fin N, (a : ℕ) < k → (b : ℕ) = k → j.val a b = 0) :
    ρ j (avg ρ L k x w) = L.chi j • avg ρ L k x w := by
  obtain ⟨h1, hm, -, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  simp only [mem_iff_isUp hL] at h1 hm hc
  have hi := inv_mem_of_mul_mem _ h1 hm
  obtain ⟨u, hu, hub, hn⟩ := exists_block hj hk
  have hnu : IsUp g N (u⁻¹ * j) := hm _ _ (hi _ hu) hj
  obtain ⟨n, rfl⟩ : ∃ n, j = u * n := ⟨u⁻¹ * j, by simp⟩
  rw [inv_mul_cancel_left] at hn hnu
  have e1 : ρ n (avg ρ L k x w) = L.chi n • avg ρ L k x w := by
    unfold avg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hh : InBlock k (v * w) := InBlock.mul _ _ (mem_blockUp.1 hv).2 hw
    generalize v * w = h at hh
    have hc' := conj_entry hh hn
    have hup : IsUp g N (h⁻¹ * (n * h)) :=
      ⟨fun a => by rw [hc' a a (by omega)]; exact hnu.1 a,
        fun a b hab => by
          have : (b : ℕ) < a := hab
          rw [hc' a b (by omega)]; exact hnu.2 a b hab⟩
    have hchi : L.chi (h⁻¹ * (n * h)) = L.chi n := chi_congr hL fun a b hab => hc' a b (by omega)
    have : ρ n (ρ h x) = ρ h (ρ (h⁻¹ * (n * h)) x) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
    rw [map_smul, this, hx _ hup, hchi, map_smul, smul_comm]
  have e2 : ρ u (avg ρ L k x w) = L.chi u • avg ρ L k x w := by
    unfold avg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_bijective (fun v => u * v) (Group.mulLeft_bijective u) ?_ ?_
    · intro v
      simp only [mem_blockUp]
      refine ⟨fun h => ⟨hm _ _ hu h.1, InBlock.mul _ _ hub h.2⟩, fun h => ?_⟩
      have := And.intro (hm _ _ (hi _ hu) h.1) (InBlock.mul _ _ hub.inv h.2)
      rwa [inv_mul_cancel_left] at this
    · intro v hv
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_assoc, hc _ _ hu (mem_blockUp.1 hv).1, smul_smul,
        mul_inv, mul_inv_cancel_left₀ (chi_ne_zero L u)]
  rw [map_mul, Module.End.mul_apply, e1, map_smul, e2, smul_smul, hc _ _ hu hnu, mul_comm]

theorem avg_independent [FiniteDimensional ℂ M] {L : Lev g N} (hL : L.sharp = false) {x : M} (hx0 : x ≠ 0)
    (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) {k : ℕ} (hk : k < N) (R : Finset (GG g N))
    (hR : ∀ w ∈ R, InBlock k w ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b)
    (hχ : ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → InBlock k u → InBlock k u' →
      u * w = w * u' → L.chi u = L.chi u') :
    LinearIndependent ℂ fun w : R => avg ρ L k x w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc w₀
  let φ : GG g N → ℂ := fun h =>
    ∑ w : R, ∑ u ∈ blockUp g N k, if h = u * w then c w * (L.chi u)⁻¹ else 0
  have hφ : ∀ h, φ h ≠ 0 → InBlock k h := by
    intro h hh
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
    obtain ⟨u, hu, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have : h = u * w := by by_contra hne; exact hw (if_neg hne)
    rw [this]
    exact InBlock.mul _ _ (mem_blockUp.1 hu).2 (hR w w.2).1
  have hsum : ∑ h, φ h • ρ h x = 0 := by
    rw [← hc]
    simp only [φ, avg, Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [ite_smul, mul_smul]
  have key : ∑ u' ∈ blockUp g N k, φ (w₀ * u') * L.chi u' = 0 := by
    refine Eq.trans (Finset.sum_congr ?_ fun _ _ => rfl)
      (GlobalTheory.T.whittaker_translates_corner_linearIndependent g N M ρ L hL x hx0 hx k hk φ hφ hsum w₀)
    ext u
    simp only [mem_blockUp, Finset.mem_filter, Finset.mem_univ, true_and, InBlock]
  have h2 : ∀ u' ∈ blockUp g N k, φ (w₀ * u') * L.chi u' =
      c w₀ * ((((blockUp g N k).filter fun u => w₀ * u' = u * w₀).card : ℕ) : ℂ) := by
    intro u' hu'
    have hu' := mem_blockUp.1 hu'
    simp only [φ]
    rw [Finset.sum_eq_single w₀, Finset.card_filter, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun u hu => ?_
      have hu := mem_blockUp.1 hu
      split_ifs with h
      · rw [hχ w₀ w₀.2 u u' hu.1 hu'.1 hu.2 hu'.2 h.symm, mul_assoc, inv_mul_cancel₀ (chi_ne_zero L u')]
        simp
      · simp
    · intro w _ hw
      refine Finset.sum_eq_zero fun u hu => if_neg fun h => hw (Subtype.ext ?_)
      exact GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset g N w w₀ u u' (hR w w.2).2 (hR w₀ w₀.2).2 (mem_blockUp.1 hu).1 hu'.1 h.symm
    · simp
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Nat.cast_sum, mul_eq_zero] at key
  refine key.resolve_right ?_
  have h1 : (1 : GG g N) ∈ blockUp g N k :=
    mem_blockUp.2 ⟨(mem_iff_isUp hL 1).1 (GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L).1, inBlock_one k⟩
  rw [Nat.cast_eq_zero, Finset.sum_eq_zero_iff]
  intro h
  have := h 1 h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
  exact this h1 (by simp)

theorem card_le_rk [FiniteDimensional ℂ M] (L : Lev g N) {ι : Type} [Fintype ι] (x : ι → M)
    (hx : LinearIndependent ℂ x) (he : ∀ i u, L.Mem u → ρ u (x i) = L.chi u • x i) :
    Fintype.card ι ≤ rk ρ L.e := by
  obtain ⟨h1, hm, hc1, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  exact (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L.Mem L.chi h1 hm hc1 hc).2.2.2 _ (x ∘ (Fintype.equivFin ι).symm)
    (hx.comp _ (Fintype.equivFin ι).symm.injective) fun i => he _

theorem exists_unit_coeff [FiniteDimensional ℂ M] (hρ : IsGeneric ρ) :
    ∃ L : Lev g N, L.sharp = false ∧ (∀ a, L.co a = 1) ∧
      ∃ x : M, x ≠ 0 ∧ ∀ u, IsUp g N u → ρ u x = L.chi u • x := by
  obtain ⟨L, hL, x, hx0, hx⟩ := hρ
  let L₁ : Lev g N := { L with co := fun _ => 1 }
  have hL₁ : L₁.sharp = false := hL
  refine ⟨L₁, hL₁, fun _ => rfl, ?_⟩
  have h1 := card_le_rk ρ L (fun _ : Unit => x) (linearIndependent_unique_iff.2 hx0)
    fun _ u hu => hx u hu.1
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L₁ rfl rfl rfl, Fintype.card_unit] at h1
  obtain ⟨⟨y, hy⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h1
  obtain ⟨h1, hm, hc1, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L₁
  refine ⟨y, fun h => hy0 (Subtype.ext h), fun u hu => ?_⟩
  exact ((GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L₁.Mem L₁.chi h1 hm hc1 hc).2.2.1 y).1 hy u ((mem_iff_isUp hL₁ u).2 hu)

end GlobalTheory.BadShare.FirstRows

namespace GlobalTheory.BadShare
open FirstRows

theorem rk_ge_of_isGeneric_of_s_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 →
    (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  intro g hg N M _ _ _ ρ hρ L hL hs
  obtain ⟨L₁, hL₁, hco, x, hx0, hx⟩ := exists_unit_coeff ρ hρ
  let L' : Lev g N := { L with ψ := L₁.ψ, hψ := L₁.hψ, co := L₁.co }
  have hkN : L.k < N := by have := L.hk; omega
  have hmem : ∀ u, L'.Mem u → ∀ a b : Fin N, (a : ℕ) < L.k → (b : ℕ) = L.k → u.val a b = 0 := by
    intro u hu a b ha hb
    exact hu.2 hL a b (by simp [L', hs]) (by simpa [L', hs] using ha) (by simpa [L', hs] using hb)
  have hchi : ∀ u, L'.Mem u → L'.chi u = L₁.chi u := by
    intro u hu
    unfold Lev.chi
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : L'.Edge a b ↔ ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.k) := by
      simp only [Lev.Edge, L', hL, hs, if_true]
      omega
    have e2 : L₁.Edge a b ↔ (b : ℕ) = a + 1 := by simp [Lev.Edge, hL₁]
    by_cases h1 : (b : ℕ) = a + 1
    · rw [if_pos (e2.2 h1)]
      by_cases h2 : (a : ℕ) + 1 = L.k
      · rw [if_neg (fun h => (e1.1 h).2 h2), hmem u hu a b (by omega) (by omega), mul_zero]
      · rw [if_pos (e1.2 ⟨h1, h2⟩)]
    · rw [if_neg (fun h => h1 (e1.1 h).1), if_neg (fun h => h1 (e2.1 h))]
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' rfl rfl rfl]
  have hg0 : (0 : ℝ) < g := Nat.cast_pos.2 hg.out.pos
  rcases Nat.eq_zero_or_pos L.k with hk | hk
  · have h1 := card_le_rk ρ L' (fun _ : Unit => x) (linearIndependent_unique_iff.2 hx0)
      fun _ u hu => by rw [hchi u hu]; exact hx u hu.1
    rw [Fintype.card_unit] at h1
    have h1 : (1 : ℝ) ≤ rk ρ L'.e := by exact_mod_cast h1
    have : 0 < 1 / (g : ℝ) := by positivity
    rw [hk, pow_zero]
    linarith
  · obtain ⟨R, hcard, hR, hχ⟩ := GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum g N L₁ hL₁ hco L.k hk hkN
    have h1 := card_le_rk ρ L' _ (avg_independent ρ hL₁ hx0 hx hkN R hR hχ) fun w u hu => by
      rw [hchi u hu]; exact avg_eigen ρ hL₁ hx (hR w w.2).1 hu.1 (hmem u hu)
    rw [Fintype.card_coe] at h1
    have h2 : (((g - 1) * g ^ (L.k - 1) : ℕ) : ℝ) ≤ rk ρ L'.e := by exact_mod_cast hcard.trans h1
    rw [Nat.cast_mul, Nat.cast_sub hg.out.pos, Nat.cast_pow, Nat.cast_one] at h2
    refine le_of_eq_of_le ?_ h2
    obtain ⟨m, hm⟩ : ∃ m, L.k = m + 1 := ⟨L.k - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    field_simp

end GlobalTheory.BadShare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirstStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | exact GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | (intros; apply GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero <;> assumption)
end
