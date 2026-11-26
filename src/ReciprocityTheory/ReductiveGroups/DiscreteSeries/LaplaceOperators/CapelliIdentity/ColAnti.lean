module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

def permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)

theorem permIns_zero {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : permIns i τ 0 = i := by
  simp [permIns, Equiv.Perm.mul_apply]

theorem permIns_succ {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) (j : Fin p) :
    permIns i τ j.succ = i.succAbove (τ j) := by
  simp [permIns, Equiv.Perm.mul_apply]

theorem sign_permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permIns i τ) : ℤˣ) : ℤ) = (-1) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤˣ) : ℤ) := by
  simp [permIns, Equiv.Perm.sign_mul]

theorem permIns_bijective {p : ℕ} :
    Function.Bijective (fun q : Fin (p + 1) × Equiv.Perm (Fin p) => permIns q.1 q.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have h' : permIns i τ = permIns i' τ' := h
    have hi : i = i' := by
      have h0 := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ 0) h'
      simpa only [permIns_zero] using h0
    subst hi
    have hτ : τ = τ' := by
      refine Equiv.ext fun j => ?_
      have hj := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ j.succ) h'
      simp only [permIns_succ] at hj
      first
      | exact Fin.succAbove_right_injective hj
      | exact Fin.succAbove_right_inj.mp hj
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

theorem sum_perm_succ {M : Type*} [AddCommMonoid M] {p : ℕ} (F : Equiv.Perm (Fin (p + 1)) → M) :
    ∑ σ, F σ = ∑ i, ∑ τ, F (permIns i τ) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (permIns_bijective (p := p))) F, Fintype.sum_prod_type]
  all_goals rfl

theorem basic_zsmul_sign {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (i : ℕ) (s : ℤ) (a b : 𝒰) :
    ((-1 : ℤ) ^ i * s) • (a * b) = (-1 : ℂ) ^ i • (a * (s • b)) := by
  have h1 : ((-1 : ℂ) ^ i) = (((-1 : ℤ) ^ i : ℤ) : ℂ) := by simp
  rw [h1, Int.cast_smul_eq_zsmul ℂ, mul_smul_comm, mul_smul]
  all_goals rfl

theorem basic_sign_mul_sign {p : ℕ} (τ σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ((Equiv.Perm.sign (τ * σ) : ℤˣ) : ℤ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, Equiv.Perm.sign_mul, ← mul_assoc, Int.units_mul_self, one_mul]

theorem basic_eq_zero_of_eq_neg {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰] (c : 𝒰)
    (h : c = ((-1 : ℤˣ) : ℤ) • c) : c = 0 := by
  have h' : c = -c := by
    first
    | (rw [Units.val_neg, Units.val_one, neg_one_smul] at h; exact h)
    | (simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h; exact h)
  have h2 : (2 : ℂ) • c = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h']
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem basic_swap_of_not_inj {α : Type*} {p : ℕ} (R : Fin p → α) (h : ¬ Function.Injective R) :
    ∃ i j : Fin p, i ≠ j ∧ R ∘ Equiv.swap i j = R := by
  have hex : ∃ i j, R i = R j ∧ i ≠ j := by
    by_contra hc
    push_neg at hc
    exact h fun a b hab => hc a b hab
  obtain ⟨i, j, hij, hne⟩ := hex
  refine ⟨i, j, hne, funext fun k => ?_⟩
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hij]
  · rw [h2, hij]
  · rfl

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem cminor_succ_col {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ (i : ℕ)) •
      (capEntry E x (R i) (C 0) * cminor E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1)) := by
  have e : ∀ t : ℂ, x - (t + 1) = x - 1 - t := fun t => by ring
  unfold cminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one, e, Function.comp_apply,
    basic_zsmul_sign]

theorem cminor_perm_rows {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p)) (x : ℂ) :
    cminor E (R ∘ τ) C x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  unfold cminor
  rw [Finset.smul_sum]
  refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulLeft τ) _)
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, smul_smul, basic_sign_mul_sign, Function.comp_apply]

theorem cminor_rows_not_inj {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) (h : ¬ Function.Injective R) :
    cminor E R C x = 0 := by
  obtain ⟨i, j, hij, hR⟩ := basic_swap_of_not_inj R h
  have h1 := cminor_perm_rows E R C (Equiv.swap i j) x
  rw [hR, Equiv.Perm.sign_swap hij] at h1
  exact basic_eq_zero_of_eq_neg _ h1

theorem rminor_succ_row {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      (capEntry E (x - (p : ℂ)) (R 0) (C j) * rminor E (R ∘ Fin.succ) (C ∘ j.succAbove) x) := by
  have e1 : x - ((p : ℂ) + 1) + 1 = x - p := by ring
  have e2 : ∀ t : ℂ, x - (p : ℂ) + (t + 1) = x - p + 1 + t := fun t => by ring
  unfold rminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, e1, e2, Function.comp_apply,
    basic_zsmul_sign]

theorem glRelR_op (hE : GlRelR E) : GlRelR (fun a b => MulOpposite.op (E b a)) := by
  intro a b c d
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op, hE d c b a]
  split_ifs <;> simp_all

end Ring

section Module

theorem basic_prod_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    (l : M →ₗ[ℂ] R') : ∀ {m : ℕ} (f : Fin m → Module.End ℂ M) (g : Fin m → Module.End ℂ R'),
    (∀ j, l ∘ₗ f j = g j ∘ₗ l) → l ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ l
  | 0, f, g, _ => by simp [Module.End.one_eq_id]
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      basic_prod_intertwine l _ _ (fun j => h j.succ), ← LinearMap.comp_assoc]

theorem cminor_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    {n k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (D : Fin k → Fin k → Module.End ℂ R')
    (ι : Fin k → Fin n) (hι : Function.Injective ι) (l : M →ₗ[ℂ] R')
    (hl : ∀ i j, l ∘ₗ E (ι i) (ι j) = D i j ∘ₗ l) {p : ℕ} (Rw Cw : Fin p → Fin k) (x : ℂ) :
    l ∘ₗ cminor E (ι ∘ Rw) (ι ∘ Cw) x = cminor D Rw Cw x ∘ₗ l := by
  have hc : ∀ (y : ℂ) (a b : Fin k), l ∘ₗ capEntry E y (ι a) (ι b) = capEntry D y a b ∘ₗ l := by
    intro y a b
    have hv : ∀ v, l (E (ι a) (ι b) v) = D a b (l v) := fun v => LinearMap.congr_fun (hl a b) v
    unfold capEntry
    simp only [hι.eq_iff]
    ext v
    split_ifs <;> simp [hv]
  have key : ∀ σ : Equiv.Perm (Fin p),
      l ∘ₗ (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) ((ι ∘ Rw) (σ j)) ((ι ∘ Cw) j)).prod =
        (List.ofFn fun j : Fin p => capEntry D (x - ((j : ℕ) : ℂ)) (Rw (σ j)) (Cw j)).prod ∘ₗ l := by
    intro σ
    apply basic_prod_intertwine
    intro j
    exact hc _ _ _
  unfold cminor
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := LinearMap.congr_fun (key σ) v
  simp only [LinearMap.comp_apply] at h1
  first
  | (rw [LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h1])
  | simp [h1, map_zsmul]

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capEntry_eq_add_smul (x : ℂ) (a b : Fin n) :
    capEntry E x a b = E a b + (if a = b then x else 0) • (1 : 𝒰) := by
  unfold capEntry
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

private theorem add_smul_one_mul_sub_eq_neg_swap_of_commutator (A B C D : 𝒰) (a b c d x : ℂ)
    (h1 : A * B - B * A = c • D - d • C) (h2 : D * C - C * D = b • A - a • B) :
    (A + (a * x) • (1 : 𝒰)) * (B + (b * (x - 1)) • (1 : 𝒰)) -
        (C + (c * x) • (1 : 𝒰)) * (D + (d * (x - 1)) • (1 : 𝒰)) =
      -((D + (d * x) • (1 : 𝒰)) * (C + (c * (x - 1)) • (1 : 𝒰)) -
        (B + (b * x) • (1 : 𝒰)) * (A + (a * (x - 1)) • (1 : 𝒰))) := by
  have hBA : B * A = A * B - (c • D - d • C) := by rw [← h1]; abel
  have hCD : C * D = D * C - (b • A - a • B) := by rw [← h2]; abel
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hBA, hCD]
  module

theorem capEntry_two (hE : GlRelR E) (i k j l : Fin n) (x : ℂ) :
    capEntry E x i j * capEntry E (x - 1) k l - capEntry E x k j * capEntry E (x - 1) i l =
      -(capEntry E x i l * capEntry E (x - 1) k j - capEntry E x k l * capEntry E (x - 1) i j) := by
  have hs : ∀ (a b : Fin n) (y : ℂ),
      capEntry E y a b = E a b + ((if a = b then (1 : ℂ) else 0) * y) • (1 : 𝒰) := by
    intro a b y
    rw [capEntry_eq_add_smul]
    split_ifs <;> simp
  have hd : ∀ (a b : Fin n) (u : 𝒰), (if b = a then u else 0) = (if a = b then (1 : ℂ) else 0) • u := by
    intro a b u
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h1 := hE i j k l
  have h2 := hE i l k j
  rw [hd, hd] at h1 h2
  simp only [hs]
  exact add_smul_one_mul_sub_eq_neg_swap_of_commutator (E i j) (E k l) (E k j) (E i l) _ _ _ _ x h1 h2


omit [Algebra ℂ 𝒰] in
theorem prod_ofFn_split_adj {p : ℕ} (f : Fin (p + 1) → 𝒰) (j : Fin p) : ∃ P Q : 𝒰, ∀ g : Fin (p + 1) → 𝒰,
    (∀ m, m ≠ j.castSucc → m ≠ j.succ → g m = f m) →
      (List.ofFn g).prod = P * g j.castSucc * g j.succ * Q := by
  induction p with
  | zero => exact j.elim0
  | succ q ih =>
    cases j using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun m : Fin q => f m.succ.succ).prod, fun g hg => ?_⟩
      have hr : (List.ofFn fun m : Fin q => g m.succ.succ) = List.ofFn fun m : Fin q => f m.succ.succ := by
        congr 1
        funext m
        apply hg
        · intro h; have := congrArg Fin.val h; simp at this
        · intro h; have := congrArg Fin.val h; simp at this
      simp only [List.ofFn_succ, List.prod_cons]
      rw [hr]
      simp [mul_assoc]
    | succ j' =>
      obtain ⟨P', Q', hPQ⟩ := ih (fun m => f m.succ) j'
      refine ⟨f 0 * P', Q', fun g hg => ?_⟩
      have h0 : g 0 = f 0 := hg 0
        (by intro h; have := congrArg Fin.val h; simp at this)
        (by intro h; have := congrArg Fin.val h; simp at this)
      have hc : j'.castSucc.succ = j'.succ.castSucc := Fin.ext (by simp)
      have h' := hPQ (fun m => g m.succ) (fun m hm1 hm2 =>
        hg m.succ (fun h => hm1 (Fin.succ_injective _ (h.trans hc.symm)))
          (fun h => hm2 (Fin.succ_injective _ h)))
      try dsimp only at h'
      rw [List.ofFn_succ, List.prod_cons, h', h0, hc]
      simp only [mul_assoc]

private theorem sum_eq_zero_of_add_equiv_apply_eq_zero {M α : Type*} [AddCommGroup M] [Module ℂ M] [Fintype α]
    (e : α ≃ α) (G : α → M) (h : ∀ a, G a + G (e a) = 0) : ∑ a, G a = 0 := by
  have h2 : ∑ a, G a + ∑ a, G (e a) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun a _ => h a)
  rw [Equiv.sum_comp e G, ← two_smul ℂ] at h2
  have h4 : ((1 / 2 : ℂ) * 2) • ∑ a, G a = 0 := by rw [← smul_smul, h2, smul_zero]
  rwa [show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h4

theorem cminor_swap_adj (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin p) (x : ℂ) :
    cminor E R (C ∘ Equiv.swap j.castSucc j.succ) x = -cminor E R C x := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (p + 1)), τ = Equiv.swap j.castSucc j.succ := ⟨_, rfl⟩
  rw [← hτ]
  have hab : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  have hτa : τ j.castSucc = j.succ := by rw [hτ]; exact Equiv.swap_apply_left _ _
  have hτb : τ j.succ = j.castSucc := by rw [hτ]; exact Equiv.swap_apply_right _ _
  have hτm : ∀ m, m ≠ j.castSucc → m ≠ j.succ → τ m = m := fun m h1 h2 => by
    rw [hτ]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hsg : ∀ σ : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign (σ * τ) : ℤˣ) : ℤ) = -((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    intro σ
    rw [Equiv.Perm.sign_mul, hτ, Equiv.Perm.sign_swap hab]
    simp
  have hxb : x - ((j.succ : ℕ) : ℂ) = x - ((j.castSucc : ℕ) : ℂ) - 1 := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]; ring
  rw [eq_neg_iff_add_eq_zero]
  unfold cminor
  rw [← Finset.sum_add_distrib]
  apply sum_eq_zero_of_add_equiv_apply_eq_zero (Equiv.mulRight τ)
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Function.comp_apply, hsg, neg_smul]
  obtain ⟨P, Q, hPQ⟩ := prod_ofFn_split_adj
    (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) j
  have h1 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) (fun m _ _ => rfl)
  have h2 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  have h3 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C m))
    (fun m h h' => by simp only [hτm m h h'])
  have h4 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  simp only [hτa, hτb, hxb] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  have hx := eq_neg_iff_add_eq_zero.mp (capEntry_two E hE (R (σ j.castSucc)) (R (σ j.succ))
    (C j.castSucc) (C j.succ) (x - ((j.castSucc : ℕ) : ℂ)))
  have hz := congrArg (fun t => ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (P * t * Q)) hx
  simp only [mul_zero, zero_mul, smul_zero] at hz
  rw [← hz]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, mul_assoc]
  abel

theorem cminor_perm_cols (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p))
    (x : ℂ) : cminor E R (C ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  cases p with
  | zero =>
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ q =>
    let S : Submonoid (Equiv.Perm (Fin (q + 1))) :=
      { carrier := {σ | ∀ C' : Fin (q + 1) → Fin n,
          cminor E R (C' ∘ σ) x = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • cminor E R C' x}
        mul_mem' := by
          intro a b ha hb
          have ha' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ a) x = ((Equiv.Perm.sign a : ℤˣ) : ℤ) • cminor E R C' x := ha
          have hb' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ b) x = ((Equiv.Perm.sign b : ℤˣ) : ℤ) • cminor E R C' x := hb
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ ⇑(a * b)) x = ((Equiv.Perm.sign (a * b) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hb', ha', smul_smul, Equiv.Perm.sign_mul,
            Units.val_mul, mul_comm]
        one_mem' := by
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ (1 : Equiv.Perm (Fin (q + 1)))) x =
              ((Equiv.Perm.sign (1 : Equiv.Perm (Fin (q + 1))) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          simp }
    have hle : Submonoid.closure (Set.range fun i : Fin q => Equiv.swap i.castSucc i.succ) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      show ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ Equiv.swap i.castSucc i.succ) x =
          ((Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) : ℤˣ) : ℤ) • cminor E R C' x
      intro C'
      rw [cminor_swap_adj E hE, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne, Units.val_neg,
        Units.val_one, neg_smul, one_smul]
    have hτ : τ ∈ S := hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top τ)
    have hτ' : ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C' x := hτ
    exact hτ' C

theorem cminor_cols_not_inj (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ)
    (h : ¬ Function.Injective C) : cminor E R C x = 0 := by
  obtain ⟨i, k, hik, hC⟩ := basic_swap_of_not_inj C h
  apply basic_eq_zero_of_eq_neg
  have := cminor_perm_cols E hE R C (Equiv.swap i k) x
  rw [hC, Equiv.Perm.sign_swap hik] at this
  exact this

theorem cminor_col_at (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin (p + 1)) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by
  have hπ := cminor_perm_cols E hE R C (permIns j 1) x
  rw [sign_permIns, Equiv.Perm.sign_one, Units.val_one, mul_one] at hπ
  have h0 := cminor_succ_col E R (C ∘ permIns j 1) x
  have hC0 : (C ∘ permIns j 1) 0 = C j := by rw [Function.comp_apply, permIns_zero]
  have hCs : (C ∘ permIns j 1) ∘ Fin.succ = C ∘ j.succAbove := by
    funext m
    simp only [Function.comp_apply, permIns_succ, Equiv.Perm.one_apply]
  rw [hC0, hCs, hπ] at h0
  have hsq : cminor E R C x =
      ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (j : ℕ)) • cminor E R C x) := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [hsq, h0, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
