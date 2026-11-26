module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
namespace KStar.Tree

open Polynomial IntermediateField in
private theorem totient_le_of_cyc_pow_eq_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) (h : ∀ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n = 1) (k : ℕ) :
    Nat.totient (l ^ k) ≤ Module.finrank ℚ E * n := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hl := (Fact.out : l.Prime)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hint : IsIntegral E ζ := (hζ.isIntegral (pow_pos hl.pos k)).tower_top
  set S : Finset ℤ_[l] := (Polynomial.nthRoots n (1 : ℤ_[l])).toFinset with hSdef
  have hS : S.card ≤ n := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  have hsub : ∀ r ∈ (minpoly E ζ).rootSet Ω, r ∈ S.image fun x => ζ ^ (PadicInt.toZModPow k x).val := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have hmin : minpoly E r = minpoly E ζ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr.2 (minpoly.monic hint)).symm
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hmin
    have hspec := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut Gal(Ω/E) Ω g) ζ hζ.pow_eq_one
    rw [Finset.mem_image]
    refine ⟨((cyc l E Ω g : ℤ_[l]ˣ) : ℤ_[l]), ?_, ?_⟩
    · rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn),
        ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · rw [← hg]
      exact hspec.symm
  have hdeg : (minpoly E ζ).natDegree ≤ n := by
    rw [← Polynomial.card_rootSet_eq_natDegree (K := Ω) (minpoly.irreducible hint).separable
      (IsAlgClosed.splits ((minpoly E ζ).map (algebraMap E Ω)))]
    calc Fintype.card ((minpoly E ζ).rootSet Ω) = ((minpoly E ζ).rootSet Ω).toFinset.card :=
          (Set.toFinset_card _).symm
      _ ≤ (S.image fun x => ζ ^ (PadicInt.toZModPow k x).val).card :=
          Finset.card_le_card fun x hx => hsub x (Set.mem_toFinset.1 hx)
      _ ≤ S.card := Finset.card_image_le
      _ ≤ n := hS
  haveI : FiniteDimensional E E⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ E⟮ζ⟯ := Module.Finite.trans E E⟮ζ⟯
  have hζF : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩ : E⟮ζ⟯) (l ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := (E⟮ζ⟯).val) hζ Subtype.val_injective
  have hq : (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ k) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζF (pow_pos hl.pos k)]
    exact minpoly.natDegree_le _
  calc (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := hq
    _ = Module.finrank ℚ E * Module.finrank E E⟮ζ⟯ := (Module.finrank_mul_finrank ℚ E E⟮ζ⟯).symm
    _ ≤ Module.finrank ℚ E * n := by
        apply Nat.mul_le_mul_left
        rw [IntermediateField.adjoin.finrank hint]
        exact hdeg

theorem exists_cyc_pow_ne_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) : ∃ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n ≠ 1 := by
  have hl := (Fact.out : l.Prime)
  by_contra hne
  push_neg at hne
  have key := totient_le_of_cyc_pow_eq_one l E Ω n hn hne (Module.finrank ℚ E * n + 1)
  rw [Nat.totient_prime_pow_succ hl] at key
  have h1 : Module.finrank ℚ E * n < l ^ (Module.finrank ℚ E * n) := Nat.lt_pow_self hl.one_lt
  have h2 : l ^ (Module.finrank ℚ E * n) ≤ l ^ (Module.finrank ℚ E * n) * (l - 1) :=
    Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hl.one_lt)
  omega

end KStar.Tree
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
namespace KStar.Tree

variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

private theorem isUnit_of_not_dvd {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one c)
    (not_lt.1 fun h => hc ((PadicInt.norm_lt_one_iff_dvd c).1 h))

private theorem nuOf_mem (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ g, ¬ (l : ℤ_[l]) ^ (nuOf l ε n + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  obtain ⟨g, hg⟩ := h
  have hx : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    apply hg
    ext
    exact congrArg (fun x : ℤ_[l] => (x : Padic l)) h1
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨u, v, hxv⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = u * (l : ℤ_[l]) ^ v :=
    ⟨_, _, PadicInt.unitCoeff_spec hx⟩
  have hne : {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}.Nonempty := by
    refine ⟨v, g, ?_⟩
    intro hd
    rw [hxv, pow_succ, mul_comm (u : ℤ_[l])] at hd
    have hlu : (l : ℤ_[l]) ∣ u := (mul_dvd_mul_iff_left (pow_ne_zero v hl0)).1 hd
    have hlunit : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_unit hlu u.isUnit
    have h1 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    rw [PadicInt.isUnit_iff] at hlunit
    linarith
  exact Nat.sInf_mem hne

theorem pow_nuOf_dvd (g : Γ) : (l : ℤ_[l]) ^ nuOf l ε n ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos (nuOf l ε n) with h0 | hpos
  · rw [h0, pow_zero]
    exact one_dvd _
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : k < nuOf l ε n := by omega
    have hnm : k ∉ {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1} :=
      Nat.notMem_of_lt_sInf hlt
    rw [hk]
    by_contra hd
    exact hnm ⟨g, hd⟩

theorem exists_eq_pow_nuOf_mul_unit (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ (g : Γ) (u : ℤ_[l]ˣ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = (l : ℤ_[l]) ^ nuOf l ε n * u := by
  obtain ⟨g, hg⟩ := nuOf_mem l ε n h
  obtain ⟨c, hc⟩ := pow_nuOf_dvd l ε n g
  refine ⟨g, (isUnit_of_not_dvd l (c := c) ?_).unit, ?_⟩
  · rintro ⟨d, rfl⟩
    exact hg ⟨d, by rw [hc]; ring⟩
  · rw [IsUnit.unit_spec]
    exact hc

theorem le_nuOf_iff (h : ∃ g, ε g ^ n ≠ 1) (k : ℕ) :
    k ≤ nuOf l ε n ↔ ∀ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  constructor
  · intro hk g
    exact (pow_dvd_pow _ hk).trans (pow_nuOf_dvd l ε n g)
  · intro hk
    by_contra hlt
    push_neg at hlt
    obtain ⟨g, hg⟩ := nuOf_mem l ε n h
    exact hg ((pow_dvd_pow _ hlt).trans (hk g))

theorem nuOf_pos_of_res (h : ∃ g, ε g ^ n ≠ 1) {K : Type} [CommRing K] [Nontrivial K] (θ : ℤ_[l] →+* K)
    (h1 : ∀ g, θ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1) : 0 < nuOf l ε n := by
  have key := (le_nuOf_iff l ε n h 1).2 ?_
  · omega
  intro g
  rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p]
  apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top θ)
  rw [RingHom.mem_ker, map_sub, map_pow, map_one, h1 g, sub_self]

end KStar.Tree
end
