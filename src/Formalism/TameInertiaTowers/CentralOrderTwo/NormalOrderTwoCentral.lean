module

public import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic
public import Formalism.TameInertiaTowers.StatementField

@[expose] public section

section -- merged from Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral
namespace Formalism.TwoAdicCyclotomicDecomposition

theorem normalOrderTwoCentral : NormalOrderTwoCentral := by
  intro H _ N hN h2 z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · simp [hz1]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h2
  have e1 : (⟨g * z * g⁻¹, hc⟩ : N) = y := huniq _ (by
    intro h; apply hz1
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have e2 : (⟨z, hz⟩ : N) = y := huniq _ (by
    intro h; exact hz1 (congrArg Subtype.val h))
  have : g * z * g⁻¹ = z := congrArg Subtype.val (e1.trans e2.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [this]

lemma v24 : padicValInt 2 ((5 : ℤ) ^ 2 - 1) = 3 := by
  have : ((5 : ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, Nat.multiplicity_mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

lemma v4 : padicValInt 2 ((5 : ℤ) - 1) = 2 := by
  have : ((5 : ℤ) - 1) = ((2 ^ 2 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

theorem twistVal : TwistVal := by
  intro s e he
  have h5 : Odd (5 : ℤ) := by decide
  have h52 : (5 : ℤ) ^ 2 ≠ 1 := by norm_num
  have hpos : 0 < 2 ^ s * e := Nat.mul_pos (Nat.two_pow_pos s) he
  have key := (twoAdicVal 5 h5 h52 (2 ^ s * e) hpos).1
  rw [key]
  split_ifs with hev
  · rw [v24, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by positivity) (by omega), Nat.padicValNat_def, Nat.multiplicity_prime_pow]
    omega
  · rw [v4]
    have hs : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · exfalso; apply hev
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
        exact ⟨2 ^ k * e, by ring⟩
    subst hs
    have he' : ¬ 2 ∣ e := by
      intro hd; apply hev; simpa using (even_iff_two_dvd.mpr hd)
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd he']

lemma gcd_two_pow (N k : ℕ) (hk : k ≠ 0) : Nat.gcd (2 ^ N) k = 2 ^ min N (padicValNat 2 k) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv : padicValNat 2 (2 ^ v * m) = v := by
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by positivity) hm0, Nat.padicValNat_def, Nat.multiplicity_prime_pow, Nat.padicValNat_def,
      multiplicity_eq_zero_of_not_dvd hm, add_zero]
  rw [hv]
  have hcop : Nat.Coprime m (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]
  rcases le_total N v with h | h
  · rw [min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]

theorem coinvLength : CoinvLength := by
  intro N u _ hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hsub : AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N)) =
      AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)) := by
    rcases Int.natAbs_eq (u - 1) with h | h
    · rw [h]; simp [hkdef]
    · rw [h]; simp [hkdef]
  rw [hsub]
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have hc := AddSubgroup.card_mul_index (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)))
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hN, Nat.card_zmod] at hc
  have hidx : (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))).index = Nat.gcd (2 ^ N) k := by
    have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
    have hd : 2 ^ N / Nat.gcd (2 ^ N) k * Nat.gcd (2 ^ N) k = 2 ^ N := Nat.div_mul_cancel hg
    have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
      Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
    exact Nat.eq_of_mul_eq_mul_left hdpos (hc.trans hd.symm)
  rw [← AddSubgroup.index, hidx, gcd_two_pow N k hk]
  simp [hkdef, padicValInt, Nat.padicValNat_def]

theorem genusAbelian : GenusAbelian := by
  intro G _ _ A B C hsup hcard a ha b hb c hc habc
  let f : A × B × C →* G := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hf : ∀ x : A × B × C, f x = (x.1 : G) * ((x.2.1 : G) * (x.2.2 : G)) := fun x => rfl
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hsup]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx; exact ⟨(⟨x, hx⟩, 1, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, ⟨x, hx⟩, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, 1, ⟨x, hx⟩), by simp [hf]⟩
  have hbij : Function.Bijective f := by
    apply hsurj.bijective_of_nat_card_le
    rw [Nat.card_prod, Nat.card_prod, hcard, mul_assoc]
  have h1 : f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) = f 1 := by
    rw [hf, map_one]; simpa [mul_assoc] using habc
  have h2 := hbij.1 h1
  simp only [Prod.mk_eq_one, Subgroup.mk_eq_one] at h2
  exact ⟨h2.1, h2.2.1, h2.2.2⟩

theorem pGroupGen : PGroupGen := by
  intro p _ H _ _ hP S hS
  by_contra hne
  obtain ⟨Mx, hMx, hle⟩ := (eq_top_or_exists_le_coatom (Subgroup.closure S)).resolve_left hne
  have := hP.isNilpotent
  have hMn : Mx.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Mx (Group.normalizerCondition_of_isNilpotent) hMx
  have : Subgroup.normalClosure S ≤ Mx :=
    Subgroup.normalClosure_le_normal (fun x hx => hle (Subgroup.subset_closure hx))
  rw [hS] at this
  exact hMx.1 (top_le_iff.mp this)

end Formalism.TwoAdicCyclotomicDecomposition
end

section -- merged from Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
namespace Formalism.TwoAdicCyclotomicDecomposition

namespace AdmissibleUnits

def r4 (N : ℕ) (h : 4 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 4 :=
  (ZMod.castHom h (ZMod 4)).toMonoidHom.comp (Units.coeHom _)

def r8 (N : ℕ) (h : 8 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 8 :=
  (ZMod.castHom h (ZMod 8)).toMonoidHom.comp (Units.coeHom _)

lemma mod_four_reduction_five (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (u5 N) = 1 := by
  unfold u5
  show (ZMod.castHom h (ZMod 4)) ((5 : ℕ) : ZMod (2 ^ N)) = 1
  rw [map_natCast]
  decide

lemma mod_four_reduction_neg_one (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 4)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

lemma mod_eight_reduction_three (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (u3 N) = 3 := by
  unfold u3
  show (ZMod.castHom h (ZMod 8)) ((3 : ℕ) : ZMod (2 ^ N)) = 3
  rw [map_natCast]
  decide

lemma mod_eight_reduction_neg_one (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 8)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

lemma neg_one_ne_one (n : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ 1 := by
  intro h
  have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
  have := congrArg (r4 (n + 2) h4) h
  rw [mod_four_reduction_neg_one, map_one] at this
  exact absurd this (by decide)

lemma mem_zpowers_nat {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = y := by
  exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h)

lemma neg_not_mem_five (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 2)))ˣ) ∉ Subgroup.zpowers (u5 (n + 2)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
  have := congrArg (r4 (n + 2) h4) hk
  rw [map_pow, mod_four_reduction_five, mod_four_reduction_neg_one, one_pow] at this
  exact absurd this (by decide)

lemma neg_not_mem_three (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u3 (n + 3)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h8 : 8 ∣ 2 ^ (n + 3) := ⟨2 ^ n, by ring⟩
  have := congrArg (r8 (n + 3) h8) hk
  rw [map_pow, mod_eight_reduction_three, mod_eight_reduction_neg_one] at this
  have h9 : (3 : ZMod 8) ^ 2 = 1 := by decide
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [pow_mul, h9, one_pow] at this
    exact absurd this (by decide)
  · rw [pow_succ, pow_mul, h9, one_pow, one_mul] at this
    exact absurd this (by decide)

lemma card_units (n : ℕ) : Nat.card (ZMod (2 ^ (n + 1)))ˣ = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n)]
  simp

private lemma exists_one_add_two_pow_odd_pow_two_pow_eq (i m0 : ℕ) : ∀ k : ℕ, ∃ m : ℕ,
    (1 + 2 ^ (i + 2) * (2 * m0 + 1)) ^ (2 ^ k) = 1 + 2 ^ (k + (i + 2)) * (2 * m + 1) := by
  intro k
  induction k with
  | zero => exact ⟨m0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (i + k) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 k, pow_mul, hm]
    ring

private lemma natCast_one_add_two_pow_mul_eq_one (N q : ℕ) : ((1 + 2 ^ N * q : ℕ) : ZMod (2 ^ N)) = 1 := by
  have h : ((2 ^ N : ℕ) : ZMod (2 ^ N)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero, Nat.cast_one]

private lemma natCast_one_add_two_pow_odd_ne_one (N m : ℕ) :
    ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) ≠ 1 := by
  intro h
  have h' : ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) = ((1 : ℕ) : ZMod (2 ^ (N + 1))) := by
    rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).1 h'.symm
  rw [Nat.add_sub_cancel_left, pow_succ] at h2
  have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos N) h2
  omega

private lemma unitOfCoprime_pow_eq_one_iff (N a e : ℕ) (h : Nat.Coprime a (2 ^ N)) :
    (ZMod.unitOfCoprime a h) ^ e = 1 ↔ ((a ^ e : ℕ) : ZMod (2 ^ N)) = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_pow]

lemma orderOf_five_units_two_pow (n : ℕ) : orderOf (u5 (n + 2)) = 2 ^ n := by
  unfold u5
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 n
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 (n + 1)
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_mul_eq_one _ _

lemma orderOf_three_units_two_pow (n : ℕ) : orderOf (u3 (n + 3)) = 2 ^ (n + 1) := by
  unfold u3
  apply orderOf_eq_prime_pow
  · rw [unitOfCoprime_pow_eq_one_iff]
    cases n with
    | zero => decide
    | succ n =>
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n
      rw [pow_succ 2 n, pow_mul' 3 (2 ^ n) 2,
        show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
  · rw [unitOfCoprime_pow_eq_one_iff]
    obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n
    rw [pow_succ 2 n, pow_mul' 3 (2 ^ n) 2,
      show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]
    exact natCast_one_add_two_pow_mul_eq_one _ _

lemma sign_eq (n : ℕ) {b b' : Bool} {k k' : ℕ}
    (h : (if b then -1 else 1) * u5 (n + 3) ^ k = (if b' then -1 else 1) * u5 (n + 3) ^ k') :
    b = b' := by
  have h4 : 4 ∣ 2 ^ (n + 3) := ⟨2 ^ (n + 1), by ring⟩
  have hr : ∀ c : Bool, r4 (n + 3) h4 (if c then -1 else 1) = if c then -1 else 1 := by
    intro c
    cases c
    · exact map_one _
    · exact mod_four_reduction_neg_one _ _
  have := congrArg (r4 (n + 3) h4) h
  rw [map_mul, map_mul, hr, hr, map_pow, map_pow, mod_four_reduction_five, one_pow, one_pow, mul_one, mul_one] at this
  cases b <;> cases b'
  · rfl
  · exact absurd this (by decide)
  · exact absurd this (by decide)
  · rfl

lemma inj (n : ℕ) : Function.Injective (fun p : Bool × Fin (2 ^ (n + 1)) =>
    (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)) := by
  rintro ⟨b, k⟩ ⟨b', k'⟩ h
  have h' : (if b then -1 else 1) * u5 (n + 3) ^ (k : ℕ) =
      (if b' then -1 else 1) * u5 (n + 3) ^ (k' : ℕ) := h
  have hb : b = b' := sign_eq n h'
  subst hb
  have h2 : u5 (n + 3) ^ (k : ℕ) = u5 (n + 3) ^ (k' : ℕ) := mul_left_cancel h'
  have ho : orderOf (u5 (n + 3)) = 2 ^ (n + 1) := orderOf_five_units_two_pow (n + 1)
  rw [pow_inj_mod, ho, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h2
  exact Prod.ext rfl (Fin.ext h2)

lemma zpowers_sq {G : Type*} [Group G] [Finite G] {g y : G} (hg : g ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_nat hy
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [pow_mul, hg, one_pow]
  · right
    rw [pow_succ, pow_mul, hg, one_pow, one_mul]

lemma orderOf_mk_eq {G : Type*} [CommGroup G] [Finite G] {x g : G} (hg : g ^ 2 = 1)
    (hx : g ∉ Subgroup.zpowers x) :
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = orderOf x := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd (QuotientGroup.mk' _) x
  · apply orderOf_dvd_of_pow_eq_one
    have h1 : (QuotientGroup.mk (s := Subgroup.zpowers g) x) ^
        orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = 1 := pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    rcases zpowers_sq hg h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [← h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) hx

lemma card_quot (n : ℕ) : Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸
    Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
  rw [Nat.card_zpowers, orderOf_eq_prime (neg_one_sq) (neg_one_ne_one n)] at h1
  have h2 : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
    have := card_units (n + 1)
    rw [pow_succ] at this
    exact this
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right two_pos h1).symm

end AdmissibleUnits

open AdmissibleUnits in
theorem unitsTwoPow : UnitsTwoPow := by
  unfold UnitsTwoPow
  intro n
  refine ⟨card_units (n + 2), orderOf_five_units_two_pow (n + 1), orderOf_three_units_two_pow n, neg_not_mem_five (n + 1),
    neg_not_mem_three n, ?_⟩
  intro u
  have hc : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) := card_units (n + 2)
  have hcard : Fintype.card (Bool × Fin (2 ^ (n + 1))) = Fintype.card (ZMod (2 ^ (n + 3)))ˣ := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc]
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj n, hcard⟩
  obtain ⟨p, hp⟩ := hbij.2 u
  exact ⟨p, hp.symm, fun q hq => hbij.1 (hq.symm.trans hp.symm)⟩

open AdmissibleUnits in
theorem quotCyclic : QuotCyclic := by
  unfold QuotCyclic
  intro n
  have hsq : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ^ 2 = 1 := neg_one_sq
  have h5 : orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u5 (n + 2))) = 2 ^ n := by
    rw [orderOf_mk_eq hsq (neg_not_mem_five n), orderOf_five_units_two_pow n]
  refine ⟨isCyclic_of_orderOf_eq_card _ (h5.trans (card_quot n).symm), card_quot n, h5, ?_⟩
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
    have h3 : u3 (0 + 2) = -1 := by
      unfold u3
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one]
      decide
    rw [h3]
    exact Subgroup.mem_zpowers _
  | succ n =>
    show orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ))
      (u3 (n + 3))) = 2 ^ (n + 1)
    rw [orderOf_mk_eq neg_one_sq (neg_not_mem_three n)]
    exact orderOf_three_units_two_pow n

end Formalism.TwoAdicCyclotomicDecomposition
end

section -- merged from Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
open NumberField

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

namespace UnitConjugation

lemma conj_eq_inv_of_pow_eq_one {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    starRingEnd ℂ z = z⁻¹ := by
  have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp

lemma pow_eq_inv_iff {K : Type*} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (k : ℕ) : ζ ^ k = ζ⁻¹ ↔ (k : ZMod m) = -1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have e : ζ ^ k = ζ⁻¹ ↔ ζ ^ k * ζ = 1 :=
    ⟨fun h => by rw [h, inv_mul_cancel₀ hζ0], fun h => eq_inv_of_mul_eq_one_left h⟩
  rw [e, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  exact add_eq_zero_iff_eq_neg

variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

lemma ne_zero_of_sq (hq : 0 < q) (ha : a ^ 2 = -(q : L)) : a ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at ha
  exact hq.ne' (by exact_mod_cast ha)

lemma phi_conj (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (φ : L →+* ℂ) :
    starRingEnd ℂ (φ a) = -φ a := by
  set z := φ a with hzdef
  have hz : z ^ 2 = -(q : ℂ) := by
    rw [hzdef, ← map_pow, ha, map_neg, map_natCast]
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exfalso
    have hre := Complex.conj_eq_iff_re.1 h2
    have h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q : ℝ) : ℝ) : ℂ) := by
      push_cast; rw [hre]; exact hz
    have h4 := Complex.ofReal_injective h3
    have h5 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith [sq_nonneg z.re]
  · exact h2

lemma sgn_eq_neg_one_iff (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (σ : Gal(L/ℚ)) :
    sgn σ a = -1 ↔ σ a = -a := by
  have ha0 := ne_zero_of_sq hq ha
  have hsq : σ a ^ 2 = a ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  unfold sgn
  split_ifs with hc
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h
      exfalso
      have h3 : (2 : L) * a = 0 := by linear_combination h - hc
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact two_ne_zero h4
      · exact ha0 h4
  · simp only [true_iff]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact absurd h1 hc
    · exact h1

lemma autToPow_eq_neg_one_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    hζ.autToPow ℚ σ = -1 ↔ σ ζ = ζ⁻¹ := by
  rw [← hζ.autToPow_spec ℚ σ, pow_eq_inv_iff hζ, ZMod.natCast_val, ZMod.cast_id, Units.ext_iff,
    Units.val_neg, Units.val_one]

lemma galMap_eq_JJ_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    galMap hζ a b σ = JJ n ↔ hζ.autToPow ℚ σ = -1 ∧ sgn σ a = -1 ∧ sgn σ b = -1 := by
  simp only [galMap, JJ, Prod.mk.injEq]

lemma algAdjoin_eq_top (h : IsLayer n q d ζ a b) : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), h.2.2.2]
  rfl

theorem conj_iff (hq : 0 < q) (hd : 0 < d) (h : IsLayer n q d ζ a b) (φ : L →+* ℂ)
    (σ : Gal(L/ℚ)) :
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n := by
  obtain ⟨hζ, ha, hb, _⟩ := h
  have hφζ : (φ ζ) ^ (2 ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hconj : starRingEnd ℂ (φ ζ) = φ (ζ⁻¹) := by
    rw [map_inv₀, conj_eq_inv_of_pow_eq_one (pow_ne_zero n two_ne_zero) hφζ]
  rw [galMap_eq_JJ_iff, autToPow_eq_neg_one_iff, sgn_eq_neg_one_iff hq ha,
    sgn_eq_neg_one_iff hd hb]
  constructor
  · intro hx
    refine ⟨φ.injective ?_, φ.injective ?_, φ.injective ?_⟩
    · rw [hx, hconj]
    · rw [hx, map_neg, phi_conj hq ha]
    · rw [hx, map_neg, phi_conj hd hb]
  · rintro ⟨h1, h2, h3⟩
    have heq : (φ.comp (σ : L →+* L)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top ⟨hζ, ha, hb, ‹_›⟩)
      intro x hx
      simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change φ (σ x) = starRingEnd ℂ (φ x)
      rcases hx with rfl | rfl | rfl
      · rw [h1, hconj]
      · rw [h2, map_neg, phi_conj hq ha]
      · rw [h3, map_neg, phi_conj hd hb]
    intro x
    have := congrArg (fun f => f x) heq
    simpa using this

end UnitConjugation

open UnitConjugation

theorem layerConj_of (_hG : LayerGalois) : LayerConj := by
  intro n q d _ hqd L _ _ ζ a b h φ σ
  exact conj_iff hqd.1.pos hqd.2.1.pos h φ σ

theorem layerReal_of (hG : LayerGalois) (hC : LayerConj) : LayerReal := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hGal, hfin, _hmul, hbij⟩ := hG n q d hn hqd L ζ a b h
  have h1 : ∀ (φ : L →+* ℂ) (σ : Gal(L/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n :=
    fun φ σ => hC n q d hn hqd L ζ a b h φ σ
  have hq : 0 < q := hqd.1.pos
  obtain ⟨σc, hσc⟩ := hbij.2 (JJ n)
  have hTC : IsTotallyComplex L := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw a
    rw [ComplexEmbedding.conjugate_coe_eq, phi_conj hq h.2.1] at h2
    have h3 : (2 : ℂ) * w.embedding a = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (ne_zero_of_sq hq h.2.1) h4
  have hCM : IsCMField L := by
    refine IsCMField.of_forall_isConj L (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact ((h1 φ σc).2 hσc x).symm
  have h5 : ∀ x : L, x ∈ maximalRealSubfield L ↔
      ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx σ hσ
      let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
      apply φ.injective
      rw [(h1 φ σ).2 hσ x]
      exact hx φ
    · intro hx φ
      have := (h1 φ σc).2 hσc x
      rw [hx σc hσc] at this
      exact this.symm
  have h4 : Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n := by
    have h := (letI : Module.Free (maximalRealSubfield L) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield L) L)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L, hfin,
      pow_succ] at h
    omega
  exact ⟨hCM, h5, h4⟩

end Formalism.TwoAdicCyclotomicDecomposition
end
end
