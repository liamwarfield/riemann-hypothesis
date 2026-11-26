module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem cyc_mem_princ_iff (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (g : G F Ω) :
    cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ ∀ t : Ω, t ^ l ^ n = 1 → g t = t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ F Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  have hpow : ∀ t : Ω, t ^ l ^ n = 1 → t ^ (1 : ZMod (l ^ n)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  rw [h1]
  constructor
  · intro h t ht
    have := cyclotomicCharacter.spec l g.toRingEquiv t ht
    rw [h, hpow t ht] at this
    exact this
  · intro h
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ ht'

private theorem le_finrank (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ)
    (h : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) : c ≤ Module.finrank ℚ L := by
  have hl : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := h
  have h1 : (l ^ c).totient ≤ Module.finrank ℚ L := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ c) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hl.pos c)]
    exact minpoly.natDegree_le ζ
  rcases c with _ | c
  · exact Nat.zero_le _
  · rw [Nat.totient_prime_pow_succ hl] at h1
    have h2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
    have h4 : l ^ c * 1 ≤ l ^ c * (l - 1) := Nat.mul_le_mul_left _ h3
    omega

private theorem ex_iff (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L := by
  have hl : l.Prime := Fact.out
  have hb : BddAbove {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)} := ⟨_, fun c hc => le_finrank L l c hc⟩
  refine ⟨fun h => le_csSup hb h, fun h => ?_⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ cZero l L) :=
    Nat.sSup_mem (s := {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)}) ⟨0, 1, by simp⟩ hb
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  exact ⟨ζ ^ l ^ d, hζ.pow (pow_pos hl.pos _) (by rw [hd, pow_add, mul_comm])⟩

private theorem all_iff (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l c) ↔ ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : IsGalois L Ω := IsGalois.mk
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ c)
    obtain ⟨ζ, rfl⟩ : ξ ∈ Set.range (algebraMap L Ω) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed ξ).2 fun g =>
        (cyc_mem_princ_iff L Ω l c g).1 (h g) ξ hξ.pow_eq_one
    exact ⟨ζ, hξ.of_map_of_injective (algebraMap L Ω).injective⟩
  · rintro ⟨ζ, hζ⟩ g
    have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ c) := hζ.map_of_injective (algebraMap L Ω).injective
    refine (cyc_mem_princ_iff L Ω l c g).2 fun t ht => ?_
    obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one ht
    rw [map_pow, g.commutes]

theorem UpperTheory.V.Tower.muQ :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], (∀ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L) ∧ (∀ c : ℕ, Un L Ω l c = ⊤ ↔ c ≤ cZero l L) ∧
        (HasMuQ l L ↔ qExp l ≤ cZero l L) ∧ (HasMuQ l L → IsTotallyComplex L ∧ Procyc L Ω l) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L) := by
  intro L Ω _ _ _ _ _ l _
  have hl : l.Prime := Fact.out
  have hq : (if l = 2 then 4 else l) = l ^ qExp l := by
    unfold qExp
    split_ifs with h
    · subst h; rfl
    · rw [pow_one]
  have hP : Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L := by
    by_cases h : l = 2
    · have h2 : qExp l = 2 := if_pos h
      rw [Procyc, HasMuQ, hq, h2, ← all_iff L Ω l 2]
      rfl
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  refine ⟨ex_iff L l, fun c => ?_, ?_, fun h => ⟨?_, hP.2 (Or.inr h)⟩, hP⟩
  · rw [← ex_iff, ← all_iff L Ω, Subgroup.eq_top_iff']
    exact forall_congr' fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  · rw [HasMuQ, hq, ex_iff]
  · obtain ⟨ζ, hζ⟩ := h
    refine nrRealPlaces_eq_zero_iff.1 (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt ?_ hζ)
    have := hl.two_le
    split_ifs <;> omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem pg_emult {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) (h2 : l = 2 → 2 ≤ c) {u : ℤ_[l]}
    (hd : (l : ℤ_[l]) ^ c ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = emultiplicity (l : ℤ_[l]) (u - 1) + n := by
  have hp : Prime (l : ℕ) := (Fact.out : l.Prime).prime
  by_cases hl : l = 2
  · have hc : 2 ≤ c := h2 hl
    have hd2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 := (pow_dvd_pow _ hc).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq hd2, emultiplicity_pow_self_of_prime hp]
  · have hd1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ (by omega)).trans hd
    rw [KStar.TotallyRealRoots.emultiplicity_pow_sub_one_odd hl hd1, emultiplicity_pow_self_of_prime hp]

private theorem pg_index {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 0 < a) :
    (KStar.TotallyRealRoots.princ l a).index = l ^ (a - 1) * (l - 1) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hker : KStar.TotallyRealRoots.princ l a = (KStar.TotallyRealRoots.redPow l a).ker := rfl
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (KStar.TotallyRealRoots.redPow_surjective a),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl ha]

private theorem pg_exists {l : ℕ} [Fact l.Prime] {c : ℕ} (h1 : 1 ≤ c) :
    ∃ v ∈ KStar.TotallyRealRoots.princ l c, v ∉ KStar.TotallyRealRoots.princ l (c + 1) := by
  have hirr : Irreducible (l : ℤ_[l]) := PadicInt.irreducible_p
  have hnu : ¬ IsUnit (-((l : ℤ_[l]) ^ c)) := by
    rw [IsUnit.neg_iff, isUnit_pow_iff (by omega)]
    exact hirr.not_isUnit
  have hu : IsUnit (1 + (l : ℤ_[l]) ^ c) := by
    have := (IsLocalRing.isUnit_or_isUnit_one_sub_self (-((l : ℤ_[l]) ^ c))).resolve_left hnu
    simpa [sub_eq_add_neg] using this
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp
  · rw [KStar.TotallyRealRoots.mem_princ]
    simp only [IsUnit.unit_spec, add_sub_cancel_left]
    rw [pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit]
    omega

theorem UpperTheory.V.Tower.princGen :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℕ), qExp l ≤ c →
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, (KStar.TotallyRealRoots.princ l c ≤ (Subgroup.zpowers u).topologicalClosure ↔ u ∉ KStar.TotallyRealRoots.princ l (c + 1))) ∧
        (∀ u ∈ KStar.TotallyRealRoots.princ l c, u ∉ KStar.TotallyRealRoots.princ l (c + 1) → PropA.IsLevel l (u : ℤ_[l]) c ∧
          ∀ m : ℕ, u ^ l ^ m ∈ KStar.TotallyRealRoots.princ l (c + m) ∧ u ^ l ^ m ∉ KStar.TotallyRealRoots.princ l (c + m + 1)) ∧
        ∀ m : ℕ, (KStar.TotallyRealRoots.princ l (c + m)).relIndex (KStar.TotallyRealRoots.princ l c) = l ^ m := by
  intro l _ c hc
  have hl : l.Prime := Fact.out
  have h1 : 1 ≤ c := by
    unfold qExp at hc; split_ifs at hc <;> omega
  have h2 : l = 2 → 2 ≤ c := by
    intro h; unfold qExp at hc; simp [h] at hc; omega
  have hexact : ∀ u : ℤ_[l]ˣ, u ∈ KStar.TotallyRealRoots.princ l c → u ∉ KStar.TotallyRealRoots.princ l (c + 1) →
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = c := by
    intro u hu hu1
    rw [KStar.TotallyRealRoots.mem_princ] at hu hu1
    exact emultiplicity_eq_coe.mpr ⟨hu, hu1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    constructor
    · intro hle hu1
      have hcl : IsClosed ((KStar.TotallyRealRoots.princ l (c + 1) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
        Subgroup.isClosed_of_isOpen _ (KStar.TotallyRealRoots.isOpen_princ _)
      have hcle := Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hu1) hcl
      obtain ⟨v, hv, hv'⟩ := pg_exists (l := l) h1
      exact hv' (hcle (hle hv))
    · intro hu1
      exact KStar.TotallyRealRoots.princ_le_of_isClosed h1 h2 (Subgroup.isClosed_topologicalClosure _)
        (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)) (hexact u hu hu1)
  · intro u hu hu1
    have he := hexact u hu hu1
    refine ⟨⟨?_, h1, h2⟩, ?_⟩
    · have hpow : ∀ n : ℕ, IsDiscreteValuationRing.addVal ℤ_[l] ((l : ℤ_[l]) ^ n) = n := by
        intro n
        rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p]
        simp
      obtain ⟨hd, hnd⟩ := emultiplicity_eq_coe.mp he
      have a1 := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hd
      rw [hpow] at a1
      have a2 : ¬ (((c + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1)) := by
        intro h
        apply hnd
        apply (IsDiscreteValuationRing.addVal_le_iff_dvd).mp
        rw [hpow]
        exact h
      show IsDiscreteValuationRing.addVal ℤ_[l] ((u : ℤ_[l]) - 1) = c
      apply le_antisymm _ a1
      push_neg at a2
      push_cast at a2
      exact ENat.lt_natCast_add_one_iff.mp a2
    · intro m
      have hm := pg_emult h1 h2 (KStar.TotallyRealRoots.mem_princ.mp hu) m
      rw [he] at hm
      have hm' : emultiplicity (l : ℤ_[l]) (((u ^ l ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1) = ((c + m : ℕ) : ℕ∞) := by
        push_cast
        exact hm
      obtain ⟨a, b⟩ := emultiplicity_eq_coe.mp hm'
      exact ⟨KStar.TotallyRealRoots.mem_princ.mpr a, fun h => b (KStar.TotallyRealRoots.mem_princ.mp h)⟩
  · intro m
    have hle := KStar.TotallyRealRoots.princ_anti (l := l) (Nat.le_add_right c m)
    have key := Subgroup.relIndex_mul_index hle
    rw [pg_index (by omega : 0 < c), pg_index (by omega : 0 < c + m)] at key
    have hcm : c + m - 1 = (c - 1) + m := by omega
    rw [hcm, pow_add] at key
    have hpos : 0 < l ^ (c - 1) * (l - 1) :=
      Nat.mul_pos (pow_pos hl.pos _) (by have := hl.two_le; omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [key]
    ring
end
