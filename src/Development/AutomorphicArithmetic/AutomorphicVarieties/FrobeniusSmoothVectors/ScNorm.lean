module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

theorem UpperTheory.V.Fr.sc_norm :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : c.O), ‖(x : PadicAlgCl l)‖ ≤ 1 ∧ (x ∈ maximalIdeal c.O ↔ ‖(x : PadicAlgCl l)‖ < 1) := by
  intro l _ c x
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hle : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hu : ∀ u : c.Oˣ, ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : c.Oˣ)
    have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have h' : ((l : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : c.O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : c.O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => ?_
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h] at hl
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, h1, one_pow, mul_one] at hl
    exact absurd hl.symm (inv_lt_one_of_one_lt₀ hl1).ne
  refine ⟨hle x, fun hx => ?_, fun hx => ?_⟩
  · rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hϖ1 (hle y)
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    exact absurd (hu u) hx.ne
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hth_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span {(⟨(p : Ω), natCast_mem _ p⟩ : (⊥ : Subring Ω))}) (by
      intro h
      rw [Ideal.span_singleton_eq_top] at h
      obtain ⟨⟨b, hb⟩, hb1⟩ := isUnit_iff_exists_inv.mp h
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hb
      have h0 : ((p : Ω) * (n : Ω)) = 1 := congrArg Subtype.val hb1
      have h1 : ((p : ℤ) * n : ℤ) = 1 := by exact_mod_cast h0
      have h2 : (p : ℤ) ∣ 1 := ⟨n, h1.symm⟩
      have h3 : p ∣ 1 := by exact_mod_cast h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3))
  exact ⟨B, B.mem_nonunits_iff.mp (hB ⟨_, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hth_spec (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (w : ℕ) [hw : Fact w.Prime]
    (s : G ℚ Ω) (ζ : Ω) (h : ζ ^ w = 1) : s ζ = ζ ^ ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : ζ ^ w ^ 1 = 1 := by rwa [pow_one]
  exact cyclotomicCharacter.spec (L := Ω) w (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ h1

private theorem hth_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (w : ℕ) [hw : Fact w.Prime] (s : G ℚ Ω) :
    (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw.out.ne_zero⟩
  have hred : ∀ (ζ : Ω) (m : ℕ), ζ ^ w = 1 → ζ ^ m = ζ ^ (m % w) := by
    intro ζ m hζ
    conv_lhs => rw [← Nat.mod_add_div m w, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hcv : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val < w :=
    lt_of_lt_of_eq (ZMod.val_lt _) (pow_one w)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
    have e1 := ha ζ0 hζ0.pow_eq_one
    rw [hth_spec Ω w s ζ0 hζ0.pow_eq_one, hred ζ0 (a ^ l) hζ0.pow_eq_one] at e1
    have e2 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val = a ^ l % w :=
      hζ0.pow_inj hcv (Nat.mod_lt _ (Nat.pos_of_neZero w)) e1
    have e3 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) = (a : ZMod (w ^ 1)) ^ l := by
      apply ZMod.val_injective
      rw [e2, ← Nat.cast_pow, ZMod.val_natCast, pow_one]
    have hu : IsUnit (a : ZMod (w ^ 1)) := (isUnit_pow_iff hl0).mp (e3 ▸ (cycMod ℚ Ω w 1 s).isUnit)
    exact ⟨hu.unit, Units.ext (by simp [e3])⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u : ZMod (w ^ 1)).val, fun ζ hζ => ?_⟩
    have e : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) =
        (((u : ZMod (w ^ 1)).val ^ l : ℕ) : ZMod (w ^ 1)) := by
      rw [← hu]
      simp
    rw [hth_spec Ω w s ζ hζ, hred ζ (((u : ZMod (w ^ 1)).val) ^ l) hζ, e, hred ζ _ hζ,
      ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self w one_ne_zero)]

theorem UpperTheory.V.Fr.hth :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → IsOpen (Hth Ω l w : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hth Ω l w ∧ (Hth Ω l w).index = l ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (w : Ω) < 1 → Ine (F := ℚ) B' ≤ Hth Ω l w) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (w : Ω) < 1 → ¬ Ine (F := ℚ) B' ≤ Hth Ω l w := by
  intro Ω _ _ _ l hl w hwp hw1
  haveI hw : Fact w.Prime := ⟨hwp⟩
  haveI : Fact (w ^ 1).Prime := ⟨by rw [pow_one]; exact hwp⟩
  have hmem : ∀ s : G ℚ Ω, s ∈ Hth Ω l w ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
    intro s
    change (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ∧
      (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹ ζ = ζ ^ a ^ l) ↔ _
    rw [hth_iff Ω l w s, hth_iff Ω l w s⁻¹, map_inv, inv_mem_iff, and_self]
  have hker : (cycMod ℚ Ω w 1).ker ≤ Hth Ω l w := fun s hs =>
    (hmem s).mpr (by rw [MonoidHom.mem_ker.mp hs]; exact one_mem _)
  have hZ : ∀ s, cycMod ℚ Ω w 1 s = KStar.TotallyRealRoots.redPow w 1 (cycZ ℚ Ω w s) := fun s => rfl
  obtain ⟨A, hA⟩ := hth_place Ω w hwp
  have hsurj : Function.Surjective (cycMod ℚ Ω w 1) := by
    intro v
    obtain ⟨u, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 v
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w A hA u
    exact ⟨σ, by rw [hZ, hσ]⟩
  have hidx : (Hth Ω l w).index = l := by
    have hH : Hth Ω l w =
        (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range.comap (cycMod ℚ Ω w 1) := by
      ext s
      exact hmem s
    rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hwp]
    exact Nat.gcd_eq_right ((Nat.modEq_iff_dvd' hwp.one_lt.le).mp hw1.symm)
  refine ⟨?_, ?_, hidx, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (KStar.TotallyRealRoots.princ w 1).comap (cycZ ℚ Ω w)) ?_ ?_
    · intro s hs
      apply hker
      rw [MonoidHom.mem_ker, hZ]
      exact hs
    · exact (contTw ℚ Ω w).1.isOpen_preimage _ (KStar.TotallyRealRoots.isOpen_princ 1)
  · exact (Abelianization.commutator_subset_ker (cycMod ℚ Ω w 1)).trans hker
  · intro B' hB' s hs
    apply hker
    rw [MonoidHom.mem_ker, hZ, MonoidHom.mem_ker.mp ((places ℚ Ω w B').2.2.2 hB' hs), map_one]
  · intro B' hB' hle
    have htop : Hth Ω l w = ⊤ := by
      refine eq_top_iff.mpr fun s _ => ?_
      obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 (cycMod ℚ Ω w 1 s)
      obtain ⟨σ, hσI, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w B' hB' u
      have h1 := (hmem σ).mp (hle hσI)
      rw [hZ, hσ, hu] at h1
      exact (hmem s).mpr h1
    rw [htop, Subgroup.index_top] at hidx
    exact hl.out.one_lt.ne hidx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HlayPlace
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hlay_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hmem : (p : Ω) ∈ (⊥ : Subring Ω) := Subring.mem_bot.mpr ⟨p, by simp⟩
  set x : (⊥ : Subring Ω) := ⟨p, hmem⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb⟩ := Subring.mem_bot.mp (u⁻¹ : (⊥ : Subring Ω)ˣ).1.2
    have h1 : (u : (⊥ : Subring Ω)) * (↑u⁻¹ : (⊥ : Subring Ω)) = 1 := u.mul_inv
    have h2 : ((p : ℤ) * b : ℤ) = (1 : Ω) := by
      have := congrArg Subtype.val h1
      simp only [Subring.coe_mul, Subring.coe_one] at this
      rw [hu] at this
      push_cast
      rw [hb]
      exact this
    have h3 : (p : ℤ) * b = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨b, h3.symm⟩
    have : p ∣ 1 := by exact_mod_cast h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hlay_cop (l : ℕ) [hl : Fact l.Prime] (m : ℕ) : (l ^ m).Coprime (l - 1) := Nat.Coprime.pow_left m ((Nat.coprime_self_sub_right hl.out.one_le).mpr (Nat.coprime_one_right _))

private theorem hlay_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (h2 : l ≠ 2) :
    Nat.card ((⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1))) = l ^ m := by
  haveI := ZMod.isCyclic_units_of_prime_pow l hl.out h2 (m + 1)
  rw [← MonoidHom.range_eq_map, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out]
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  rw [Nat.gcd_comm, Nat.gcd_mul_left_right]
  exact Nat.mul_div_cancel _ hpos

private theorem hlay_inf {l : ℕ} [hl : Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) (h1 : u ∈ KStar.TotallyRealRoots.princ l 1)
    (h : KStar.TotallyRealRoots.redPow l (m + 1) u ^ (l - 1) = 1) : KStar.TotallyRealRoots.redPow l (m + 1) u = 1 := by
  set x := KStar.TotallyRealRoots.redPow l (m + 1) u with hx
  have hd : l ^ 1 ∣ l ^ (m + 1) := pow_dvd_pow l (by omega)
  set f := ZMod.unitsMap hd
  have hfx : f x = 1 := by
    have : f x = KStar.TotallyRealRoots.redPow l 1 u := by
      ext
      simp only [f, hx, ZMod.unitsMap, KStar.TotallyRealRoots.redPow, Units.coe_map, MonoidHom.coe_coe]
      exact congrArg (fun g => g (u : ℤ_[l])) (PadicInt.zmod_cast_comp_toZModPow 1 (m + 1) (by omega))
    rw [this]
    exact h1
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hd
  have hcardG : Nat.card (ZMod (l ^ (m + 1)))ˣ = l ^ m * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl.out]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out]
  have hker : Nat.card f.ker = l ^ m := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardH, hcardG] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hl.out.one_lt) e
  have hpow : x ^ (l ^ m) = 1 := by
    have := pow_card_eq_one' (G := f.ker) (x := ⟨x, hfx⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  have hdvd : orderOf x ∣ Nat.gcd (l ^ m) (l - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one h)
  rw [hlay_cop l m, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem UpperTheory.V.Fr.hlay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ), l ≠ 2 → IsOpen (Hlay Ω l m : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hlay Ω l m ∧ (Hlay Ω l m).index = l ^ m ∧ Hlay Ω l m ⊓ (cycMod ℚ Ω l 1).ker = (cycMod ℚ Ω l (m + 1)).ker ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ Hlay Ω l m) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → (Hlay Ω l m).relIndex (Ine (F := ℚ) B') = l ^ m ∧ ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
  intro Ω _ _ _ l _ m h2
  obtain ⟨A, hA⟩ := hlay_place Ω l Fact.out
  have hsurjIne : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 →
      ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
    intro B' hB' r
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := l) r y
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B' hB' v
    exact ⟨σ, hσ, by rw [← hσv]; rfl⟩
  have hidx : ∀ K : Subgroup (G ℚ Ω), K.map (cycMod ℚ Ω l (m + 1)) = ⊤ →
      (Hlay Ω l m).relIndex K = l ^ m := by
    intro K hK
    have hsub : (Hlay Ω l m).subgroupOf K = ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).ker := by
      ext x
      rfl
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    have hr : ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).range =
        (⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1)) := by
      ext y
      simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MonoidHom.pow_apply, powMonoidHom_apply]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨z, rfl⟩
        have hz : z ∈ K.map (cycMod ℚ Ω l (m + 1)) := hK ▸ Subgroup.mem_top z
        obtain ⟨k, hk, rfl⟩ := hz
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [hr]
    exact hlay_card l m h2
  have hcont := (UpperTheory.V.Base.contTw ℚ Ω l).1
  have hkerle : (cycMod ℚ Ω l (m + 1)).ker ≤ Hlay Ω l m := by
    intro σ hσ
    show (cycMod ℚ Ω l (m + 1) σ) ^ (l - 1) = 1
    rw [MonoidHom.mem_ker.mp hσ, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun B' hB' => ⟨hidx _ (hsurjIne B' hB' _), hsurjIne B' hB'⟩⟩
  · apply Subgroup.isOpen_mono hkerle
    have hset : ((cycMod ℚ Ω l (m + 1)).ker : Set (G ℚ Ω)) =
        cycZ ℚ Ω l ⁻¹' (KStar.TotallyRealRoots.princ l (m + 1) : Set ℤ_[l]ˣ) := by
      ext σ
      rfl
    rw [hset]
    exact (KStar.TotallyRealRoots.isOpen_princ (m + 1)).preimage hcont
  · exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.relIndex_top_right]
    exact hidx ⊤ (top_unique ((hsurjIne A hA _).symm.le.trans (Subgroup.map_mono le_top)))
  · apply le_antisymm
    · rintro σ ⟨h1, h1'⟩
      exact hlay_inf m (cycZ ℚ Ω l σ) h1' h1
    · intro σ hσ
      exact ⟨hkerle hσ, KStar.TotallyRealRoots.princ_anti (by omega) hσ⟩
  · intro B' hB'
    refine ((UpperTheory.V.Base.places ℚ Ω l B').2.2.2 hB').trans ?_
    intro σ hσ
    apply hkerle
    show KStar.TotallyRealRoots.redPow l (m + 1) (cycZ ℚ Ω l σ) = 1
    rw [MonoidHom.mem_ker.mp hσ, map_one]
end
