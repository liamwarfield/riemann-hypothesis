module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
open UpperTheory.V.FW

private theorem card_dual (K A : Type) [Field K] [AddCommGroup A] [Module K A] [Finite A] :
    Nat.card (Module.Dual K A) = Nat.card A := by
  exact Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv

private theorem card_addHom_mod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    [Module (ZMod l) A] : Nat.card (A →+ ZMod l) = Nat.card A := by
  rw [← card_dual (ZMod l) A]
  exact Nat.card_congr
    { toFun := fun f => f.toZModLinearMap l
      invFun := fun g => g.toAddMonoidHom
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }

private theorem card_addHom_zmod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    (h : ∀ x : A, l • x = 0) : Nat.card (A →+ ZMod l) = Nat.card A :=
  @card_addHom_mod l _ A _ _ (AddCommGroup.zmodModule h)

theorem UpperTheory.V.FW.cardTors :
    ∀ (C : Type) [CommGroup C] [Finite C], (∀ n : ℕ, (powR (C := C) n).index = Nat.card (torK (C := C) n)) ∧ ∀ (l : ℕ) [Fact l.Prime], Nat.card (C →* Multiplicative (ZMod l)) = (powR (C := C) l).index := by
  intro C _ _
  refine ⟨fun n => ?_, fun l _ => ?_⟩
  · have h1 := Subgroup.card_mul_index (powR (C := C) n)
    have h2 := Subgroup.card_mul_index (torK (C := C) n)
    have h3 : (torK (C := C) n).index = Nat.card (powR (C := C) n) := Subgroup.index_ker _
    rw [h3] at h2
    have hpos : 0 < Nat.card (powR (C := C) n) := Nat.card_pos
    have h4 : Nat.card (powR (C := C) n) * (powR (C := C) n).index
        = Nat.card (powR (C := C) n) * Nat.card (torK (C := C) n) := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  · set N := powR (C := C) l
    have hle : ∀ f : C →* Multiplicative (ZMod l), N ≤ f.ker := by
      intro f x hx
      change x ∈ (powMonoidHom l : C →* C).range at hx
      rcases MonoidHom.mem_range.mp hx with ⟨c, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow]
    have e : (C ⧸ N →* Multiplicative (ZMod l)) ≃ (C →* Multiplicative (ZMod l)) :=
      { toFun := fun g => g.comp (QuotientGroup.mk' N)
        invFun := fun f => QuotientGroup.lift N f (hle f)
        left_inv := fun g => by
          apply QuotientGroup.monoidHom_ext
          ext
          rfl
        right_inv := fun f => by
          ext
          rfl }
    rw [← Nat.card_congr e, Nat.card_congr MonoidHom.toAdditiveLeft]
    have ht : ∀ x : Additive (C ⧸ N), l • x = 0 := by
      intro x
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (Additive.toMul x)
      apply Additive.toMul.injective
      rw [toMul_nsmul, ← hc, toMul_zero, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff]
      change c ^ l ∈ (powMonoidHom l : C →* C).range
      exact MonoidHom.mem_range.mpr ⟨c, by simp [powMonoidHom_apply]⟩
    rw [card_addHom_zmod l (Additive (C ⧸ N)) ht]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcNeg
open UpperTheory.V.FW

private theorem div_sub_add_div_add_one_eq (c M a : ℕ) (hM : 0 < M) (hr : a % M ≠ 0) (ha : a < c * M) :
    (c * M - a) / M + a / M + 1 = c := by
  have hdm := Nat.div_add_mod a M
  have hrl := Nat.mod_lt a hM
  generalize a / M = k at hdm ⊢
  generalize a % M = r at hdm hrl hr
  subst hdm
  have hkc : k < c := by
    by_contra hck
    push_neg at hck
    have : M * c ≤ M * k := Nat.mul_le_mul_left M hck
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, c = k + 1 + j := ⟨c - k - 1, by omega⟩
  have e1 : (k + 1 + j) * M = M * k + M + j * M := by ring
  have hq : ((k + 1 + j) * M - (M * k + r)) / M = j := by
    apply Nat.div_eq_of_lt_le
    · rw [e1]
      omega
    · rw [e1, Nat.add_mul, Nat.one_mul]
      omega
  rw [hq]
  omega

theorem UpperTheory.V.FW.gcNeg :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → Odd c → s ≠ 0 → gc M c (-s) = -gc M c s := by
  intro M c _ s hc hodd hs
  unfold gc
  have hcu : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).mpr hc
  have ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s) := by ring
  have ht0 : (c : ZMod M)⁻¹ * s ≠ 0 := by
    intro h0
    apply hs
    calc s = ((c : ZMod M) * (c : ZMod M)⁻¹) * s := by rw [ZMod.mul_inv_of_unit _ hcu, one_mul]
      _ = (c : ZMod M) * ((c : ZMod M)⁻¹ * s) := by ring
      _ = 0 := by rw [h0, mul_zero]
  haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩
  rw [ht, ZMod.val_neg_of_ne_zero]
  have hv0 : 0 < ((c : ZMod M)⁻¹ * s).val := ZMod.val_pos.mpr ht0
  have hvM : ((c : ZMod M)⁻¹ * s).val < M := ZMod.val_lt _
  generalize ((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢
  have hMpos : 0 < M := by omega
  have hcpos : 0 < c := hodd.pos
  have hndvd : (c * v) % M ≠ 0 := by
    intro h0
    have h1 : M ∣ c * v := Nat.dvd_of_mod_eq_zero h0
    have h2 : M ∣ v := (Nat.Coprime.dvd_mul_left hc.symm).mp h1
    have := Nat.le_of_dvd hv0 h2
    omega
  have hlt : c * v < c * M := Nat.mul_lt_mul_of_pos_left hvM hcpos
  have key := div_sub_add_div_add_one_eq c M (c * v) hMpos hndvd hlt
  rw [mul_tsub]
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  generalize ((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢
  generalize (2 * m + 1) * v / M = Q at key ⊢
  push_cast
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToZModPowOneEqZeroIff
open UpperTheory.V.FW

private theorem toZModPow_one_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZModPow 1 x = 0 ↔ ‖x‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton, pow_one]

private theorem exists_root_lift {l : ℕ} [Fact l.Prime] (u : (ZMod (l ^ 1))ˣ) :
    ∃ ζ ∈ rootsOfUnity (Nat.totient (l ^ 1)) ℤ_[l], redU l 1 ζ = u := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  have ht : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hu : u ^ (l - 1) = 1 := by
    rw [← ht, ← ZMod.card_units_eq_totient]
    exact pow_card_eq_one
  have hn : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZModPow 1 a = (u : ZMod (l ^ 1)) :=
    ⟨((u : ZMod (l ^ 1)).val : ℤ_[l]), by simp⟩
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF
  have hFa : ‖F.aeval a‖ < 1 := by
    rw [← toZModPow_one_eq_zero_iff]
    have : ((u : ZMod (l ^ 1))) ^ (l - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    simp [hF, ha, this]
  have hdF : ‖(Polynomial.derivative F).aeval a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [← toZModPow_one_eq_zero_iff] at h
    have hmul : PadicInt.toZModPow 1 ((Polynomial.derivative F).aeval a) =
        ((l - 1 : ℕ) : ZMod (l ^ 1)) * ((u : ZMod (l ^ 1))) ^ (l - 1 - 1) := by
      rw [hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow]
      simp [ha]
    have hcast : ((l - 1 : ℕ) : ZMod (l ^ 1)) = -1 := by
      rw [Nat.cast_sub hl.one_le, Nat.cast_one, pow_one, ZMod.natCast_self, zero_sub]
    rw [hmul, hcast, neg_one_mul, neg_eq_zero, ← Units.val_pow_eq_pow_val] at h
    exact Units.ne_zero _ h
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hdF]; simpa using hFa)
  rw [hdF, ← toZModPow_one_eq_zero_iff, map_sub, sub_eq_zero, ha] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  refine ⟨Units.ofPowEqOne z (l - 1) hz1 hn, ?_, ?_⟩
  · rw [ht, mem_rootsOfUnity]
    exact Units.pow_ofPowEqOne _ _
  · exact Units.ext (by simp [redU, hza])

private theorem units_four (u : (ZMod (2 ^ 2))ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide

theorem UpperTheory.V.FW.teich :
    ∀ (l : ℕ) [Fact l.Prime], Function.Bijective ((redU l (ee l)).comp (WW l).subtype) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hsurj : Function.Surjective ((redU l (ee l)).comp (WW l).subtype) := by
    by_cases h2 : l = 2
    · subst h2
      intro u
      have ht : Nat.totient (2 ^ ee 2) = 2 := by decide
      rcases units_four u with h | h
      · exact ⟨1, by simp [h] <;> rfl⟩
      · refine ⟨⟨-1, ?_⟩, ?_⟩
        · show (-1 : ℤ_[2]ˣ) ∈ rootsOfUnity (Nat.totient (2 ^ ee 2)) ℤ_[2]
          rw [ht, mem_rootsOfUnity]
          simp
        · rw [h]
          exact Units.ext (by simp [redU] <;> rfl)
    · have he : ee l = 1 := if_neg h2
      have key : ∀ u : (ZMod (l ^ 1))ˣ, ∃ a : WW l, (redU l 1) a = u := by
        intro u
        obtain ⟨ζ, hζ, hred⟩ := exists_root_lift u
        exact ⟨⟨ζ, by simpa [WW, he] using hζ⟩, hred⟩
      rw [he]
      intro u
      obtain ⟨a, ha⟩ := key u
      exact ⟨a, ha⟩
  have hfin : Finite (WW l) := by
    show Finite (rootsOfUnity _ ℤ_[l])
    infer_instance
  haveI : NeZero (l ^ ee l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hc := card_rootsOfUnity ℤ_[l] (Nat.totient (l ^ ee l))
  refine hsurj.bijective_of_nat_card_le (le_trans hc (le_of_eq ?_))
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.NilCard
open UpperTheory.V.FW

private theorem card_le_card_ker_mul_card_map {V : Type} [AddCommGroup V] [Finite V] (f : V →+ V)
    (H : AddSubgroup V) :
    Nat.card H ≤ Nat.card (AddMonoidHom.ker f) * Nat.card (H.map f) := by
  set g : H →+ V := f.comp H.subtype with hg
  have h1 := AddSubgroup.card_mul_index (AddMonoidHom.ker g)
  rw [AddSubgroup.index_ker] at h1
  have h2 : AddMonoidHom.range g = H.map f := by
    rw [hg, ← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  have h3 : Nat.card (AddMonoidHom.ker g) ≤ Nat.card (AddMonoidHom.ker f) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : V), by
        have hx := x.2
        rw [AddMonoidHom.mem_ker] at hx ⊢
        exact hx⟩ : AddMonoidHom.ker f)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem UpperTheory.V.FW.nilCard :
    ∀ (V : Type) [AddCommGroup V] [Finite V] (T : AddMonoid.End V) (N : ℕ), T ^ N = 0 → Nat.card V ≤ (AddMonoidHom.range T).index ^ N := by
  intro V _ _ T N hN
  set K := Nat.card (AddMonoidHom.ker (T : V →+ V)) with hK
  have hidx : (AddMonoidHom.range (T : V →+ V)).index = K := by
    have a := AddSubgroup.card_mul_index (AddMonoidHom.ker (T : V →+ V))
    have c := AddSubgroup.index_ker (T : V →+ V)
    rw [c] at a
    have b := AddSubgroup.card_mul_index (AddMonoidHom.range (T : V →+ V))
    have hpos : 0 < Nat.card (AddMonoidHom.range (T : V →+ V)) := Nat.card_pos
    have : Nat.card (AddMonoidHom.range (T : V →+ V)) * (AddMonoidHom.range (T : V →+ V)).index
        = Nat.card (AddMonoidHom.range (T : V →+ V)) * K := by
      rw [b, ← a, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have step : ∀ k : ℕ, Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
      ≤ K * Nat.card (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by
    intro k
    have h := card_le_card_ker_mul_card_map (T : V →+ V) (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
    have e : (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)).map (T : V →+ V)
        = AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨x, ?_⟩
        rw [pow_succ']
        rfl
      · rintro ⟨x, rfl⟩
        refine ⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩
        rw [pow_succ']
        rfl
    rw [e] at h
    exact h
  have main : ∀ k : ℕ, Nat.card V
      ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Nat.one_mul]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨x, x, by rw [pow_zero]; rfl⟩ :
          AddMonoidHom.range ((T ^ 0 : AddMonoid.End V) : V →+ V))) ?_
      intro a b hab
      simpa using congrArg Subtype.val hab
    | succ k ih =>
      calc Nat.card V
          ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := ih
        _ ≤ K ^ k * (K * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V))) :=
          Nat.mul_le_mul_left _ (step k)
        _ = K ^ (k + 1) * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by ring
  have hN1 : Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) ≤ 1 := by
    have hinj : Function.Injective
        (fun _ : AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V) => ()) := by
      rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ _
      apply Subtype.ext
      show (T ^ N) x = (T ^ N) y
      rw [hN]
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  rw [hidx]
  calc Nat.card V
      ≤ K ^ N * Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) := main N
    _ ≤ K ^ N * 1 := Nat.mul_le_mul_left _ hN1
    _ = K ^ N := Nat.mul_one _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GamGen
open UpperTheory.V.FW

private theorem padic_val_one_add_mul_pow_pow_sub_one (l : ℕ) (hl : l.Prime) (f : ℕ) (hf : f.Coprime l) (j : ℕ) :
    (l : ℤ) ^ (ee l + j) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 ∧
      ¬ (l : ℤ) ^ (ee l + j + 1) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hfl : ¬ (l : ℤ) ∣ (f : ℤ) := by
    intro hd
    have hd' : l ∣ f := Int.natCast_dvd_natCast.mp hd
    exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf.symm hd')
  have hq : emultiplicity (l : ℤ) ((f : ℤ) * (l : ℤ) ^ ee l) = (ee l : ℕ∞) := by
    rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hfl,
      zero_add]
  have hx : ¬ (l : ℤ) ∣ 1 + (f : ℤ) * (l : ℤ) ^ ee l := by
    intro hd
    have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
    have h2 : (l : ℤ) ∣ (f : ℤ) * (l : ℤ) ^ ee l :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have h3 : (l : ℤ) ∣ 1 := by
      have := dvd_sub hd h2
      simpa using this
    have h4 : l ∣ 1 := by exact_mod_cast h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h4)
  have key : emultiplicity (l : ℤ) ((1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1)
      = ((ee l + j : ℕ) : ℕ∞) := by
    by_cases h2 : l = 2
    · subst h2
      have e2 : ee 2 = 2 := by simp [ee]
      have h4 : (4 : ℤ) ∣ (1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) - 1 := by
        rw [e2]
        exact ⟨f, by push_cast; ring⟩
      have hx2 : ¬ (2 : ℤ) ∣ 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2 := by
        simpa using hx
      have := Int.two_pow_two_pow_sub_pow_two_pow (x := 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2)
        (y := 1) j h4 hx2
      rw [one_pow, add_sub_cancel_left] at this
      have hq2 : emultiplicity (2 : ℤ) ((f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) = (ee 2 : ℕ∞) := by
        simpa using hq
      rw [hq2] at this
      have : emultiplicity ((2 : ℕ) : ℤ) ((1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) ^ 2 ^ j - 1)
          = (ee 2 : ℕ∞) + j := by simpa using this
      rw [this]
      push_cast
      rfl
    · have hodd : Odd l := hl.odd_of_ne_two h2
      have e1 : ee l = 1 := by simp [ee, h2]
      have hxy : (l : ℤ) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) - 1 := by
        rw [add_sub_cancel_left]
        exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
      have := Int.emultiplicity_pow_sub_pow hl hodd hxy hx (l ^ j)
      rw [one_pow, add_sub_cancel_left, hq,
        emultiplicity_pow_self_of_prime (Nat.prime_iff.mp hl) j] at this
      rw [this]
      push_cast
      rfl
  constructor
  · rw [pow_dvd_iff_le_emultiplicity, key]
  · rw [pow_dvd_iff_le_emultiplicity, key]
    norm_cast
    omega

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.FW.gamGen :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (γ : (ZMod (f * l ^ n))ˣ), f.Coprime l → ee l ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (ZMod.unitsMap h).ker = Subgroup.zpowers γ ∧ γ ^ l ^ n = 1 := by
  intro l _ f n h γ hf hen hγ
  have hl : l.Prime := Fact.out
  obtain ⟨d, rfl⟩ : ∃ d, n = ee l + d := ⟨n - ee l, by omega⟩
  have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : l = 1 := by simpa [Nat.Coprime] using hf
    exact hl.one_lt.ne' this
  haveI : NeZero (f * l ^ (ee l + d)) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  set x : ℤ := 1 + (f : ℤ) * (l : ℤ) ^ ee l with hxdef
  have hγx : (γ : ZMod (f * l ^ (ee l + d))) = ((x : ℤ) : ZMod (f * l ^ (ee l + d))) := by
    rw [hγ, hxdef]
    push_cast
    ring
  have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ (ee l + d)) := by
    rw [← Int.natCast_pow, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ hf
  have hpow : ∀ m : ℕ, γ ^ m = 1 ↔ (l : ℤ) ^ (ee l + d) ∣ x ^ m - 1 := by
    intro m
    have hfdvd : (f : ℤ) ∣ x ^ m - 1 := by
      have h1 : x - 1 ∣ x ^ m - 1 ^ m := sub_dvd_pow_sub_pow x 1 m
      rw [one_pow] at h1
      refine dvd_trans ?_ h1
      rw [hxdef, add_sub_cancel_left]
      exact dvd_mul_right _ _
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, hγx, ← Int.cast_pow,
      ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro hd
      exact dvd_trans (dvd_mul_left _ _) hd
    · intro hd
      exact hcop.mul_dvd hfdvd hd
  have hord : orderOf γ = l ^ d := by
    rcases d with _ | d
    · rw [pow_zero, orderOf_eq_one_iff]
      have h1 : γ ^ (l ^ 0) = 1 := by
        rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf 0).1
      simpa using h1
    · apply orderOf_eq_prime_pow
      · rw [hpow, hxdef, ← Nat.add_assoc]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf d).2
      · rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf (d + 1)).1
  set K := (ZMod.unitsMap h).ker with hK
  have c1 : Nat.card (ZMod (f * l ^ (ee l + d)))ˣ = (f * l ^ (ee l + d)).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have c2 : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardK : Nat.card K = l ^ d := by
    have a := Subgroup.card_mul_index K
    rw [hK, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective h),
      Subgroup.card_top, c1, c2,
      Nat.totient_mul (Nat.Coprime.pow_right _ hf), Nat.totient_mul (Nat.Coprime.pow_right _ hf),
      Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)] at a
    have hpos : 0 < f.totient * (l ^ (ee l - 1) * (l - 1)) := by
      have h1 := hl.one_lt
      have h2 := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0)
      exact Nat.mul_pos h2 (Nat.mul_pos (pow_pos hl.pos _) (by omega))
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hK, a]
    have : ee l + d - 1 = (ee l - 1) + d := by omega
    rw [this, pow_add]
    ring
  have hmem : γ ∈ K := by
    rw [hK, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, Units.val_one,
      MonoidHom.coe_coe, hγ, map_add, map_one, map_mul, map_pow, map_natCast, map_natCast]
    have h0 : ((f * l ^ ee l : ℕ) : ZMod (f * l ^ ee l)) = 0 := ZMod.natCast_self _
    push_cast at h0
    rw [h0, add_zero]
  have hle : Subgroup.zpowers γ ≤ K := (Subgroup.zpowers_le).mpr hmem
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, ?_⟩
  · rw [Nat.card_zpowers, hord, hcardK]
  · rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact pow_dvd_pow l (by omega)
end
