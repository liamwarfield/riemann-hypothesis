module

public import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EmultiplicityEqValuation
namespace LevelStatements.Ln03

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem pow_dvd_iff_le_valuation (x : ℤ_[l]) (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  first
  | (rw [← Ideal.mem_span_singleton]; exact PadicInt.mem_span_pow_iff_le_valuation x hx n)
  | (rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow];
     exact PadicInt.norm_le_pow_iff_le_valuation x hx n)

theorem emultiplicity_prime_eq_valuation (x : ℤ_[l]) (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = x.valuation := by
  rw [emultiplicity_eq_coe]
  refine ⟨(pow_dvd_iff_le_valuation x hx _).2 le_rfl, fun h => ?_⟩
  have := (pow_dvd_iff_le_valuation x hx _).1 h
  omega

theorem not_dvd_natCast (b : ℕ) (hb : ¬ l ∣ b) : ¬ (l : ℤ_[l]) ∣ (b : ℤ_[l]) := by
  intro h
  apply hb
  obtain ⟨c, hc⟩ := h
  have h2 := congrArg (PadicInt.toZMod : ℤ_[l] →+* ZMod l) hc
  simp only [map_natCast, map_mul, CharP.cast_eq_zero, ZMod.natCast_self, zero_mul] at h2
  exact (CharP.cast_eq_zero_iff (ZMod l) l b).1 h2

theorem toZModPow_eq_one_iff (k : ℕ) (x : ℤ_[l]) (hx : x - 1 ≠ 0) :
    PadicInt.toZModPow k x = 1 ↔ k ≤ (x - 1).valuation := by
  have h1 : PadicInt.toZModPow k x = 1 ↔ PadicInt.toZModPow k (x - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
  rw [h1, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    pow_dvd_iff_le_valuation _ hx]

private theorem prime_natCast_padicInt : Prime (l : ℤ_[l]) := by
  first
  | exact PadicInt.prime_p
  | exact UniqueFactorizationMonoid.irreducible_iff_prime.mp PadicInt.irreducible_p
  | exact PadicInt.irreducible_p.prime

theorem factV (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1) (m : ℕ) (hm : m ≠ 0) :
    (u ^ m - 1).valuation = 1 + padicValNat l m := by
  have hl := (Fact.out : l.Prime)
  have hprime : Prime (l : ℤ_[l]) := prime_natCast_padicInt
  have hu0 : u - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hu
    omega
  have hdvd : (l : ℤ_[l]) ∣ u - 1 := by
    have := (pow_dvd_iff_le_valuation (u - 1) hu0 1).2 (by rw [hu])
    rwa [pow_one] at this
  have hndvd : ¬ (l : ℤ_[l]) ∣ u := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ 1 := by
      have := dvd_sub h hdvd
      rwa [sub_sub_cancel] at this
    exact hprime.not_unit (isUnit_of_dvd_one h1)
  have hodd : Odd l := hl.odd_of_ne_two hl2
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm l hl.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hm' (dvd_zero l)
  have hval : padicValNat l (l ^ e * m') = e := by
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hl.ne_zero) hm'0, (show padicValNat l (l ^ e) = e from by
        simpa only [← Nat.padicValNat_def] using (Nat.multiplicity_prime_pow e)),
      (show padicValNat l m' = 0 from by
        simpa only [← Nat.padicValNat_def] using (multiplicity_eq_zero_of_not_dvd hm')), add_zero]
  rw [hval]
  have hE1 : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + e := by
    have h : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1 ^ (l ^ e)) =
        emultiplicity (l : ℤ_[l]) (u - 1) + e := by
      first
      | exact emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
      | exact multiplicity.emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
      | exact multiplicity.pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
    rwa [one_pow] at h
  have hE2 : emultiplicity (l : ℤ_[l]) ((u ^ (l ^ e)) ^ m' - 1) =
      emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) := by
    have hx1 : (l : ℤ_[l]) ∣ u ^ (l ^ e) - 1 := by
      have := sub_dvd_pow_sub_pow u 1 (l ^ e)
      rw [one_pow] at this
      exact hdvd.trans this
    have hx2 : ¬ (l : ℤ_[l]) ∣ u ^ (l ^ e) := fun h => hndvd (hprime.dvd_of_dvd_pow h)
    have hx3 : ¬ (l : ℤ_[l]) ∣ (m' : ℤ_[l]) := not_dvd_natCast m' hm'
    have h : emultiplicity (l : ℤ_[l]) ((u ^ (l ^ e)) ^ m' - 1 ^ m') =
        emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) := by
      first
      | exact emultiplicity_pow_sub_pow_of_prime hprime hx1 hx2 hx3
      | exact multiplicity.emultiplicity_pow_sub_pow_of_prime hprime hx1 hx2 hx3
      | exact multiplicity.pow_sub_pow_of_prime hprime hx1 hx2 hx3
    rwa [one_pow] at h
  have htot : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e * m') - 1) = ((1 + e : ℕ) : ℕ∞) := by
    rw [pow_mul, hE2, hE1, emultiplicity_prime_eq_valuation _ hu0, hu]
    first
    | norm_cast
    | simp
  have hne : u ^ (l ^ e * m') - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at htot
    first
    | exact ENat.top_ne_coe _ htot
    | simp at htot
  rw [emultiplicity_prime_eq_valuation _ hne] at htot
  exact_mod_cast htot

theorem orderOf_u (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1) (s : ℕ) :
    orderOf (PadicInt.toZModPow (s + 1) u) = l ^ s := by
  have hl := (Fact.out : l.Prime)
  have key : ∀ j : ℕ, (PadicInt.toZModPow (s + 1) u) ^ (l ^ j) = 1 ↔ s ≤ j := by
    intro j
    have hv := factV hl2 u hu (l ^ j) (pow_ne_zero _ hl.ne_zero)
    rw [(show padicValNat l (l ^ j) = j from by
      simpa only [← Nat.padicValNat_def] using (Nat.multiplicity_prime_pow j))] at hv
    have hne : u ^ (l ^ j) - 1 ≠ 0 := by
      intro h
      rw [h, PadicInt.valuation_zero] at hv
      omega
    rw [← map_pow, toZModPow_eq_one_iff _ _ hne, hv]
    omega
  cases s with
  | zero =>
    rw [pow_zero]
    exact orderOf_eq_one_iff.mpr ((pow_one _).symm.trans
      (by simpa only [pow_zero] using (key 0).2 le_rfl))
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [key]
      omega
    · exact (key (n + 1)).2 le_rfl

variable {LL : Type*} [Field LL] [CharZero LL]

theorem isPrimitiveRoot_pow_eq_pow_iff_zmod_eq {N : ℕ} [NeZero N] {ξ : LL} (hξ : IsPrimitiveRoot ξ N) (a b : ℕ) :
    ξ ^ a = ξ ^ b ↔ (a : ZMod N) = b := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmod : ∀ c : ℕ, ξ ^ c = ξ ^ (c % N) := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c N, pow_add, pow_mul, hξ.pow_eq_one, one_pow, one_mul]
  have hz : (a : ZMod N) = b ↔ a % N = b % N := by
    first
    | exact ZMod.natCast_eq_natCast_iff' a b N
    | (rw [ZMod.natCast_eq_natCast_iff]; rfl)
  rw [hz, hmod a, hmod b]
  exact ⟨fun h => hξ.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) h, fun h => by rw [h]⟩

private theorem mem_primitiveRoots_iff_isPrimitiveRoot {k : ℕ} (h0 : 0 < k) {ζ : LL} :
    ζ ∈ primitiveRoots k LL ↔ IsPrimitiveRoot ζ k := by
  first
  | exact mem_primitiveRoots h0
  | (haveI : NeZero k := ⟨h0.ne'⟩; exact mem_primitiveRoots)

theorem pow_mem_Rs (s : ℕ) (a : (ZMod (l ^ (s + 1)))ˣ) {ξ : LL}
    (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL) :
    ξ ^ (a : ZMod (l ^ (s + 1))).val ∈ primitiveRoots (l ^ (s + 1)) LL := by
  have h0 : 0 < l ^ (s + 1) := pow_pos (Fact.out : l.Prime).pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)

theorem Rs_transitive (s : ℕ) {ξ η : LL} (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL)
    (hη : η ∈ primitiveRoots (l ^ (s + 1)) LL) :
    ∃! a : (ZMod (l ^ (s + 1)))ˣ, ξ ^ (a : ZMod (l ^ (s + 1))).val = η := by
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos (Fact.out : l.Prime).pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ hη
  obtain ⟨i, -, hi⟩ : ∃ i < l ^ (s + 1), ξ ^ i = η := by
    first
    | exact hξ.eq_pow_of_pow_eq_one hη.pow_eq_one
    | exact hξ.eq_pow_of_pow_eq_one hη.pow_eq_one h0
  have hcop : i.Coprime (l ^ (s + 1)) := by
    first
    | exact (hξ.pow_iff_coprime h0 i).1 (hi ▸ hη)
    | exact (hξ.pow_iff_coprime i).1 (hi ▸ hη)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · simp only [ZMod.coe_unitOfCoprime]
    rw [← hi, isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ, ZMod.natCast_zmod_val]
  · intro b hb
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (b : ZMod (l ^ (s + 1))),
      ← isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ]
    exact hb.trans hi.symm

private theorem isPrimitiveRoot_pow_val_mul_eq_pow_pow {N : ℕ} [NeZero N] {ξ : LL} (hξ : IsPrimitiveRoot ξ N)
    (x y : ZMod N) : ξ ^ (x * y).val = (ξ ^ x.val) ^ y.val := by
  rw [← pow_mul, isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ, Nat.cast_mul]
  first
  | rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  | simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]

theorem invariants_const (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    (f : LL → LL)
    (hfu : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (PadicInt.toZModPow (s + 1) u).val) = f ξ)
    (hfΔ : ∀ a : ZMod (l ^ (s + 1)), a ^ (l - 1) = 1 →
      ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ) :
    ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, ∀ η ∈ primitiveRoots (l ^ (s + 1)) LL, f ξ = f η := by
  have hl := (Fact.out : l.Prime)
  have hl2le := hl.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos hl.pos _
  have hmul : ∀ a b : (ZMod (l ^ (s + 1)))ˣ,
      (∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ (a : ZMod (l ^ (s + 1))).val) = f ξ) →
      (∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ (b : ZMod (l ^ (s + 1))).val) = f ξ) →
      ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
        f (ξ ^ ((a * b : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro a b ha hb ξ hξ
    have hξ' := (mem_primitiveRoots_iff_isPrimitiveRoot h0).1 hξ
    rw [Units.val_mul, isPrimitiveRoot_pow_val_mul_eq_pow_pow hξ',
      hb _ (pow_mem_Rs s a hξ), ha ξ hξ]
  have hord := orderOf_u hl2 u hu s
  have hxpow : (PadicInt.toZModPow (s + 1) u) ^ (l ^ s) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  obtain ⟨ub, hub⟩ : ∃ ub : (ZMod (l ^ (s + 1)))ˣ,
      (ub : ZMod (l ^ (s + 1))) = PadicInt.toZModPow (s + 1) u :=
    ⟨Units.ofPowEqOne _ (l ^ s) hxpow (pow_ne_zero _ hl.ne_zero), by
      first
      | exact Units.val_ofPowEqOne _ _ _ _
      | rfl⟩
  have hubord : orderOf ub = l ^ s := by
    rw [← orderOf_units, hub, hord]
  have hS_ub : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (ub : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro ξ hξ
    rw [hub]
    exact hfu ξ hξ
  have hpowS : ∀ k : ℕ, ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ ((ub ^ k : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro k
    induction k with
    | zero =>
      intro ξ hξ
      rw [pow_zero, Units.val_one]
      exact hfΔ 1 (one_pow _) ξ hξ
    | succ n ih =>
      intro ξ hξ
      rw [pow_succ ub n]
      exact hmul _ _ ih hS_ub ξ hξ
  have hcopl : Nat.Coprime l (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hw : orderOf (ub ^ (l - 1)) = l ^ s := by
    have hcop : (orderOf ub).Coprime (l - 1) := by
      rw [hubord]
      exact Nat.Coprime.pow_left s hcopl
    first
    | rw [Nat.Coprime.orderOf_pow hcop, hubord]
    | rw [orderOf_pow_coprime hcop, hubord]
    | rw [orderOf_pow' ub (by omega : l - 1 ≠ 0), hcop.gcd_eq_one, Nat.div_one, hubord]
  haveI hcyc : IsCyclic (ZMod (l ^ (s + 1)))ˣ := by
    first
    | exact ZMod.isCyclic_units_of_prime_pow l hl hl2 (s + 1)
    | exact ZMod.isCyclic_units_of_prime_pow hl hl2 (s + 1)
    | exact ZMod.isCyclic_units_prime_pow l hl hl2 (s + 1)
  have hwpow : (ub ^ (l - 1)) ^ (l ^ s) = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one _
  have hcount : ∀ b : (ZMod (l ^ (s + 1)))ˣ, b ^ (l ^ s) = 1 → ∃ k : ℕ, (ub ^ (l - 1)) ^ k = b := by
    intro b hb
    have hsub : (Finset.range (l ^ s)).image (fun k => (ub ^ (l - 1)) ^ k) ⊆
        Finset.univ.filter (fun x : (ZMod (l ^ (s + 1)))ˣ => x ^ (l ^ s) = 1) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, -, rfl⟩ := hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [pow_right_comm (ub ^ (l - 1)) k (l ^ s), hwpow, one_pow]
    have hcard : ((Finset.range (l ^ s)).image (fun k => (ub ^ (l - 1)) ^ k)).card = l ^ s := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' : i < orderOf (ub ^ (l - 1)) := by
        rw [hw]
        simpa using hi
      have hj' : j < orderOf (ub ^ (l - 1)) := by
        rw [hw]
        simpa using hj
      first
      | exact pow_injOn_Iio_orderOf hi' hj' hij
      | (have h2 := (pow_inj_mod).1 hij
         rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h2)
    have hle := IsCyclic.card_pow_eq_one_le (α := (ZMod (l ^ (s + 1)))ˣ) (pow_pos hl.pos s)
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
    have hbmem : b ∈ Finset.univ.filter (fun x : (ZMod (l ^ (s + 1)))ˣ => x ^ (l ^ s) = 1) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hb⟩
    rw [← heq, Finset.mem_image] at hbmem
    obtain ⟨k, -, hk⟩ := hbmem
    exact ⟨k, hk⟩
  have hcardG : Fintype.card (ZMod (l ^ (s + 1)))ˣ = l ^ s * (l - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl]
  have key : ∀ a : (ZMod (l ^ (s + 1)))ˣ, ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (a : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro a
    obtain ⟨k, hk⟩ := hcount (a ^ (l - 1)) (by
      rw [← pow_mul, mul_comm, ← hcardG, pow_card_eq_one])
    have ht : ((ub ^ k)⁻¹ * a) ^ (l - 1) = 1 := by
      rw [mul_pow, inv_pow, ← hk, ← pow_mul, ← pow_mul, mul_comm k]
      first
      | exact inv_mul_cancel _
      | simp
    have hSt : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
        f (ξ ^ (((ub ^ k)⁻¹ * a : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
      intro ξ hξ
      apply hfΔ _ _ ξ hξ
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    have ha : a = ub ^ k * ((ub ^ k)⁻¹ * a) := (mul_inv_cancel_left _ _).symm
    intro ξ hξ
    rw [ha]
    exact hmul _ _ (hpowS k) hSt ξ hξ
  intro ξ hξ η hη
  obtain ⟨a, ha, -⟩ := Rs_transitive s hξ hη
  have ha' : ξ ^ (a : ZMod (l ^ (s + 1))).val = η := ha
  rw [← ha', key a ξ hξ]

theorem sigma_u_order (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    {ξ : LL} (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL) (k : ℕ) :
    ξ ^ ((PadicInt.toZModPow (s + 1) u).val ^ k) = ξ ↔ l ^ s ∣ k := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos hl.pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ
  have h := isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ ((PadicInt.toZModPow (s + 1) u).val ^ k) 1
  rw [pow_one] at h
  rw [h, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_u hl2 u hu s]

end LevelStatements.Ln03
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PowValMemPrimitiveRoots
noncomputable section

namespace LevelStatements.Link

open PowerSeries

theorem pow_val_mem_primitiveRoots {LL : Type} [Field LL] (N : ℕ) (hN : 0 < N) (w : ZMod N)
    (hw : IsUnit w) {ξ : LL} (hξ : ξ ∈ primitiveRoots N LL) : ξ ^ w.val ∈ primitiveRoots N LL := by
  obtain ⟨u, rfl⟩ := hw
  rw [mem_primitiveRoots hN] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)

theorem eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] (s : ℕ) (a b : ZMod (l ^ (s + 1)))
    (ha : a ^ (l - 1) = 1) (hb : b ^ (l - 1) = 1) (hab : (l : ZMod (l ^ (s + 1))) ∣ b - a) :
    b = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  set x := b - a with hx
  have hba : b = a + x := by rw [hx]; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion
    (Polynomial.X ^ (l - 1) : Polynomial (ZMod (l ^ (s + 1)))) a x
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  rw [← hba, ha, hb] at hk
  have hlpow : (l : ZMod (l ^ (s + 1))) ^ (s + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hxpow : x ^ (s + 1) = 0 := by
    obtain ⟨t, ht⟩ := hab
    rw [ht, mul_pow, hlpow, zero_mul]
  have hkx : IsNilpotent (k * x) := ⟨s + 1, by rw [mul_pow, hxpow, mul_zero]⟩
  have hl1 : IsUnit ((l - 1 : ℕ) : ZMod (l ^ (s + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hinv : a * a ^ (l - 1 - 1) = 1 := by
    rw [← pow_succ', show l - 1 - 1 + 1 = l - 1 by omega, ha]
  have ha' : IsUnit a := ⟨⟨a, a ^ (l - 1 - 1), hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩
  have hU : IsUnit (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) :=
    hkx.isUnit_add_left_of_commute (hl1.mul (ha'.pow _)) (Commute.all _ _)
  have hx0 : x * (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) = 0 := by
    linear_combination (-1 : ZMod (l ^ (s + 1))) * hk
  have hx' : x = 0 := hU.mul_left_eq_zero.mp hx0
  exact sub_eq_zero.mp hx'

theorem exists_toZModPow_eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] {Δ : Type*} (om : Δ → ℤ_[l])
    (hom : ∀ j, om j ^ (l - 1) = 1)
    (hom' : ∀ a : ZMod l, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a) (s : ℕ)
    (a : ZMod (l ^ (s + 1))) (ha : a ^ (l - 1) = 1) :
    ∃ j, PadicInt.toZModPow (s + 1) (om j) = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : l ∣ l ^ (s + 1) := dvd_pow_self l (Nat.succ_ne_zero s)
  set π := ZMod.castHom hdvd (ZMod l) with hπ
  have hψ : π.comp (PadicInt.toZModPow (s + 1)) = (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    apply ZMod.ringHom_eq_of_ker_eq
    have m1 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (π.comp (PadicInt.toZModPow (s + 1))))
    have m2 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l))
    rw [IsLocalRing.eq_maximalIdeal m1, IsLocalRing.eq_maximalIdeal m2]
  have key : ∀ y : ZMod (l ^ (s + 1)), π y = 0 → (l : ZMod (l ^ (s + 1))) ∣ y := by
    intro y hy
    rw [← ZMod.natCast_zmod_val y, map_natCast] at hy
    obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod l) l y.val).mp hy
    refine ⟨(t : ZMod (l ^ (s + 1))), ?_⟩
    rw [← ZMod.natCast_zmod_val y, ht, Nat.cast_mul]
  have ha0 : π a ≠ 0 := by
    intro h0
    have hpa : π a ^ (l - 1) = 1 := by rw [← map_pow, ha, map_one]
    rw [h0, zero_pow (by omega)] at hpa
    exact zero_ne_one hpa
  obtain ⟨j, hj⟩ := hom' (π a) ha0
  refine ⟨j, eq_of_pow_pred_eq_one s a _ ha ?_ ?_⟩
  · rw [← map_pow, hom j, map_one]
  · have hc : π (PadicInt.toZModPow (s + 1) (om j)) = PadicInt.toZMod (om j) :=
      RingHom.congr_fun hψ (om j)
    have hk : π (PadicInt.toZModPow (s + 1) (om j) - a) = 0 := by
      rw [map_sub, hc, hj, sub_self]
    exact key _ hk

theorem map_cyclotomic_comp {O LL : Type} [CommRing O] [Field LL] [CharZero LL] [Algebra O LL]
    (ρ : PowerSeries O →ₐ[O] PowerSeries LL) (ζ : LL) (hρ : 1 + ρ X = C ζ * exp LL) (m : ℕ) :
    ρ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      Polynomial.aeval (C ζ * exp LL) (Polynomial.cyclotomic m LL) := by
  have key : ∀ p : Polynomial O, ρ (p : PowerSeries O) = Polynomial.aeval (ρ X) p := by
    intro p
    have h := Polynomial.algHom_ext (f := ρ.comp (Polynomial.coeToPowerSeries.algHom O))
      (g := Polynomial.aeval (ρ X)) (by simp)
    have hp := AlgHom.congr_fun h p
    simpa using hp
  rw [key, Polynomial.aeval_comp]
  have h1 : Polynomial.aeval (ρ X) (Polynomial.X + 1 : Polynomial O) = C ζ * exp LL := by
    rw [map_add (f := _), Polynomial.aeval_X, map_one, add_comm, hρ]
  rw [h1, ← Polynomial.map_cyclotomic m (algebraMap O LL), Polynomial.aeval_map_algebraMap]

end LevelStatements.Link
end
end

noncomputable section

namespace LevelStatements.Link

open PowerSeries IsLocalRing Formalism.ExponentWindows

abbrev Ks (LL : Type) [Field LL] (l s : ℕ) : Type :=
  ↥(primitiveRoots (l ^ (s + 1)) LL) → LL

theorem linkRing

    (hUnique : LevelStatements.Lv.RhoUniqueStatement) (hCompl : LevelStatements.Lv.SplitComplStatement)
    (hSimple : LevelStatements.Lv.CycloSimpleStatement) (hCop : LevelStatements.Lv.PsCoprimeStatement)
    (hUnit : LevelStatements.Lv.RhoUnitStatement) (hDesc : LevelStatements.Lv.DescendDvdStatement)
    (hPi : LevelStatements.Lv.PiSeriesStatement)

    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    {LL : Type} [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL]
    (ϖ : O) (hϖ : Irreducible ϖ)

    {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]
    {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
    (S : E.LevelData L c ell Λ r) {Δ D : Type} [AddCommGroup D] [Module LL D]
    [hℓ : Fact B.ℓ.Prime] (hℓ2 : B.ℓ ≠ 2) (hℓm : (B.ℓ : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (B.ℓ ^ n0))

    (ι : PowerSeries O →ₐ[O] PowerSeries O) (w : (PowerSeries O)ˣ)
    (G1 : ι X = (w : PowerSeries O) * X ^ (B.ℓ - 1))

    (φπ : PowerSeries O →ₐ[O] PowerSeries O) (hφπ : φπ X = (1 + X) ^ B.ℓ - 1)
    (G3 : ∀ a, ι (B.φ a) = φπ (ι a))

    (hPs : LevelStatements.Lv.PsCycloStatement)
    (G2 : ∃ v : (PowerSeries O)ˣ, ι B.q = (v : PowerSeries O) *
      (((Polynomial.cyclotomic B.ℓ O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))

    (ρζ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, 1 + ρζ ζ X = C ζ * exp LL)

    (R : G.LevelModel S LL (fun s => Ks LL B.ℓ s) Δ D)
    (hρ : ∀ s < ell, ∀ (a : PowerSeries O) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s a) = ρζ ζ (ι a))
    (u : Oˣ) (uZ : ℤ_[B.ℓ]) (huZ : (uZ - 1).valuation = 1)
    (ιZ : ℤ_[B.ℓ] →+* O) (hutie : ιZ uZ = (u : O))
    (hu : ∀ s < ell, ((R.lev s).u : LL) = algebraMap O LL (u : O))
    (hσ : ∀ s < ell, ∀ (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) uZ).val → (R.lev s).σ f ζ = f ζ')
    (om : Δ → ℤ_[B.ℓ]) (hom : ∀ j, om j ^ (B.ℓ - 1) = 1)
    (hom' : ∀ a : ZMod B.ℓ, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a)
    (hτ : ∀ s < ell, ∀ j (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) (om j)).val → (R.lev s).τ j f ζ = f ζ') :
    R.K1b ∧ R.HasU u ∧ (∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s ∧ (R.lev s).PhiGammaCommute) ∧ R.UnitsAt ∧ R.Compl ϖ := by
  have hp : B.ℓ.Prime := hℓ.out
  have hl1 : 0 < B.ℓ - 1 := by have := hp.two_le; omega
  have hpos : ∀ s, 0 < B.ℓ ^ (s + 1) := fun s => pow_pos hp.pos _
  have hprim : ∀ s (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      IsPrimitiveRoot (ζ : LL) (B.ℓ ^ (s + 1)) :=
    fun s ζ => (mem_primitiveRoots (hpos s)).1 ζ.2

  have hit : ∀ s a, ι ((⇑B.φ)^[s] a) = (⇑φπ)^[s] (ι a) := by
    intro s
    induction s with
    | zero => intro a; rfl
    | succ s ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', G3, ih]

  have hG : ∀ s, ∃ w' : (PowerSeries O)ˣ, ι (B.p s) = (w' : PowerSeries O) *
      (((Polynomial.cyclotomic (B.ℓ ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
    intro s
    obtain ⟨v, hv⟩ := G2
    unfold Formalism.ExponentWindows.E.Base.p
    rw [hit]
    exact hPs O B.ℓ hp φπ hφπ (ι B.q) v hv s

  have hcyc : ∀ s < ell, ∀ (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)) (m : ℕ),
      ρζ ζ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        Polynomial.aeval (C (ζ : LL) * exp LL) (Polynomial.cyclotomic m LL) :=
    fun s hs ζ m => map_cyclotomic_comp (ρζ ζ) ζ (hρζ s hs (ζ : LL) ζ.2) m

  have hK1b : R.K1b := by
    intro s hs
    obtain ⟨w', hw'⟩ := hG s
    have hcomp : ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), ∃ U : (PowerSeries LL)ˣ,
        PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s (B.p s)) =
          (U : PowerSeries LL) * X := by
      intro ζ
      obtain ⟨U, hU⟩ := hSimple LL LL (B.ℓ ^ (s + 1)) (hpos s) (ζ : LL) (exp LL)
        ((hprim s ζ).isRoot_cyclotomic (hpos s)) (constantCoeff_exp (A := LL)) (derivative_exp LL)
      refine ⟨Units.map (ρζ ζ).toMonoidHom w' * U, ?_⟩
      rw [hρ s hs, hw', map_mul, hcyc s hs, hU, Units.val_mul, Units.coe_map, mul_assoc]
      rfl
    choose U hU using hcomp
    have hdvd : (X : PowerSeries (Ks LL B.ℓ s)) ^ 1 ∣ R.ρ s (B.p s) :=
      (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s (B.p s))).1 1).2 fun ζ => by
        rw [hU ζ, pow_one]
        exact dvd_mul_left _ _
    obtain ⟨G, hG'⟩ := hdvd
    have hGu : IsUnit G := by
      refine (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 G).2).2 fun ζ => ?_
      have h := hU ζ
      rw [hG', map_mul, map_pow, map_X, pow_one, mul_comm] at h
      rw [mul_right_cancel₀ X_ne_zero h]
      exact (U ζ).isUnit
    refine ⟨hGu.unit, ?_⟩
    rw [IsUnit.unit_spec, hG', pow_one, mul_comm]

  have hUnits : R.UnitsAt := by
    intro s hs
    have hcomp : ∀ F : PowerSeries O, (∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        IsUnit (ρζ ζ (ι F))) → IsUnit (R.ρ s F) := by
      intro F hF
      exact (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s F)).2).2 fun ζ => by
        rw [hρ s hs]
        exact hF ζ
    refine ⟨hcomp X fun ζ => ?_, fun s' hs' hne => hcomp _ fun ζ => ?_⟩
    · rw [G1, map_mul, map_pow]
      refine (w.isUnit.map (ρζ ζ)).mul (IsUnit.pow _ ?_)
      rw [isUnit_iff_constantCoeff]
      have h := congrArg constantCoeff (hρζ s hs (ζ : LL) ζ.2)
      simp only [map_add (f := _), map_one, map_mul, constantCoeff_C, constantCoeff_exp, mul_one] at h
      rw [eq_sub_of_add_eq' h]
      exact (sub_ne_zero.2 ((hprim s ζ).ne_one (Nat.one_lt_pow (Nat.succ_ne_zero s) hp.one_lt))).isUnit
    · obtain ⟨w', hw'⟩ := hG s'
      rw [hw', map_mul, hcyc s hs]
      refine (w'.isUnit.map (ρζ ζ)).mul ?_
      rw [isUnit_iff_constantCoeff, LevelStatements.Lv.constantCoeff_aeval]
      simp only [map_mul, constantCoeff_C, constantCoeff_exp, mul_one]
      refine Ne.isUnit fun h0 => hne ?_
      have hroot : (Polynomial.cyclotomic (B.ℓ ^ (s' + 1)) LL).IsRoot (ζ : LL) := by
        rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
        exact h0
      have h := ((Polynomial.isRoot_cyclotomic_iff_charZero (hpos s')).1 hroot).unique (hprim s ζ)
      exact Nat.succ_injective (Nat.pow_right_injective hp.two_le h)

  have hComplR : R.Compl ϖ := by
    intro s hs k a hk
    obtain ⟨ζ, hζ⟩ := hroot
    have hζ0 : IsPrimitiveRoot (ζ ^ (B.ℓ ^ (n0 - (s + 1)))) (B.ℓ ^ (s + 1)) :=
      hζ.pow (pow_pos hp.pos _) (by rw [← pow_add]; congr 1; omega)
    have hcd := hCompl O LL B.ℓ s hp hℓm ⟨_, hζ0⟩ ρζ
      (fun ζ' hζ' => hρζ s hs ζ' ((mem_primitiveRoots (hpos s)).2 hζ')) k (ι a)
      (fun ζ' hζ' => by
        have h := (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s a)).1 k).1 hk
          ⟨ζ', (mem_primitiveRoots (hpos s)).2 hζ'⟩
        rwa [hρ s hs] at h)
    obtain ⟨w', hw'⟩ := hG s
    have hdv : ι (B.p s ^ k) ∣ ι a := by
      rw [map_pow, hw', mul_pow, ← Units.val_pow_eq_pow_val, Units.mul_left_dvd]
      exact hcd
    obtain ⟨z, hz⟩ := (hDesc O ι (B.ℓ - 1) hl1 ⟨w, G1⟩).2 _ _ hdv
    exact ⟨0, z, by rw [pow_zero, map_one, one_mul]; exact hz⟩

  have hunitu : ∀ s, IsUnit (PadicInt.toZModPow (s + 1) uZ) := fun s =>
    IsUnit.of_pow_eq_one (pow_orderOf_eq_one _)
      (by rw [LevelStatements.Ln03.orderOf_u hℓ2 uZ huZ s]; exact (pow_pos hp.pos _).ne')
  have hunitom : ∀ s j, IsUnit (PadicInt.toZModPow (s + 1) (om j)) := fun s j =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, hom j, map_one]) hl1.ne'
  have hmem : ∀ s (a : ZMod (B.ℓ ^ (s + 1))), IsUnit a →
      ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ : LL) ^ a.val ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL := fun s a ha ζ =>
    pow_val_mem_primitiveRoots _ (hpos s) a ha ζ.2
  have hsig : ∀ s < ell, ∀ (x : Ks LL B.ℓ s) (k : ℕ) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      ∃ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ' : LL) = (ζ : LL) ^ ((PadicInt.toZModPow (s + 1) uZ).val ^ k) ∧
          (⇑(R.lev s).σ)^[k] x ζ = x ζ' := by
    intro s hs x k
    induction k with
    | zero => intro ζ; exact ⟨ζ, by simp, rfl⟩
    | succ k ih =>
      intro ζ
      obtain ⟨ζ2, h2, h2'⟩ := ih ⟨_, hmem s _ (hunitu s) ζ⟩
      refine ⟨ζ2, ?_, ?_⟩
      · rw [h2]
        change ((ζ : LL) ^ _) ^ _ = _
        rw [← pow_mul, ← pow_succ']
      · rw [Function.iterate_succ_apply', hσ s hs _ ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl, h2']

  have hK1c : ∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s := by
    intro s hs
    refine ⟨fun x => ?_, fun x hxσ hxτ => ?_⟩
    · funext ζ
      obtain ⟨ζ', h1, h2⟩ := hsig s hs x (B.ℓ ^ s) ζ
      rw [h2]
      congr 1
      apply Subtype.ext
      rw [h1]
      exact (LevelStatements.Ln03.sigma_u_order hℓ2 s uZ huZ ζ.2 _).2 dvd_rfl
    · classical
      let f : LL → LL := fun y =>
        if h : y ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL then x ⟨y, h⟩ else 0
      have hfu : ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL,
          f (ξ ^ (PadicInt.toZModPow (s + 1) uZ).val) = f ξ := by
        intro ξ hξ
        have hm := hmem s _ (hunitu s) ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hσ s hs x ⟨ξ, hξ⟩ ⟨_, hm⟩ rfl
        rw [hxσ] at h
        exact h.symm
      have hfΔ : ∀ a : ZMod (B.ℓ ^ (s + 1)), a ^ (B.ℓ - 1) = 1 →
          ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ := by
        intro a ha ξ hξ
        obtain ⟨j, hj⟩ := exists_toZModPow_eq_of_pow_pred_eq_one om hom hom' s a ha
        have hm := hmem s a (IsUnit.of_pow_eq_one ha hl1.ne') ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hτ s hs j x ⟨ξ, hξ⟩ ⟨_, hm⟩ (by rw [hj])
        rw [hxτ j] at h
        exact h.symm
      have hconst := LevelStatements.Ln03.invariants_const hℓ2 s uZ huZ f hfu hfΔ
      by_cases hne : Nonempty ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)
      · obtain ⟨ξ0⟩ := hne
        refine ⟨x ξ0, ?_⟩
        funext ζ
        have h := hconst ξ0 ξ0.2 ζ ζ.2
        simp only [f, dif_pos ξ0.2, dif_pos ζ.2] at h
        simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact h
      · refine ⟨0, ?_⟩
        funext ζ
        exact absurd ⟨ζ⟩ hne

  have hK1d : ∀ s < ell, (R.lev s).PhiGammaCommute := by
    intro s hs j x
    funext ζ
    have e1 := hσ s hs ((R.lev s).τ j x) ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl
    have e2 := hτ s hs j x ⟨_, hmem s _ (hunitu s) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩ rfl
    have e3 := hτ s hs j ((R.lev s).σ x) ζ ⟨_, hmem s _ (hunitom s j) ζ⟩ rfl
    have e4 := hσ s hs x ⟨_, hmem s _ (hunitom s j) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩
      (by
        change ((ζ : LL) ^ _) ^ _ = ((ζ : LL) ^ _) ^ _
        rw [← pow_mul, ← pow_mul, mul_comm])
    rw [e1, e2, e3, e4]
  exact ⟨hK1b, fun s hs => hu s hs, fun s hs => ⟨hK1c s hs, hK1d s hs⟩, hUnits, hComplR⟩

end LevelStatements.Link
