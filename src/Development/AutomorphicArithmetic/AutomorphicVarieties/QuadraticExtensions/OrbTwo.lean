module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DecIndex
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxAdic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem two_pow_dvd_intCast_padic_iff (k : ℤ) (n : ℕ) : (2 : ℤ_[2]) ^ n ∣ (k : ℤ_[2]) ↔ (2 : ℤ) ^ n ∣ k := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (k : ℤ_[2]) n).symm.trans
    (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := k) (n := n))
  rw [Ideal.mem_span_singleton] at h
  exact_mod_cast h

private theorem index_closed_dyadic_subgroup (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p a : ℕ) (hH : IsClosed (H : Set ℤ_[2]ˣ))
    (hu : u ∈ H) (hp : (u : ℤ_[2]) = p) (ha : 2 ≤ a) (h1 : (2 : ℤ) ^ a ∣ (p : ℤ) ^ 2 - 1)
    (h2 : ¬ (2 : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ 2 - 1) (h3 : ¬ (2 : ℤ) ^ a ∣ (p : ℤ) - 1) :
    H.index ≠ 0 ∧ 2 * H.index ≤ Nat.totient (2 ^ a) := by
  have hu2 : ((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = (((p : ℤ) ^ 2 - 1 : ℤ) : ℤ_[2]) := by
    push_cast [Units.val_pow_eq_pow_val, hp]
    ring
  have hem : emultiplicity ((2 : ℕ) : ℤ_[2]) (((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1) = (a : ℕ∞) := by
    rw [emultiplicity_eq_coe, hu2]
    simp only [Nat.cast_ofNat, two_pow_dvd_intCast_padic_iff]
    exact ⟨h1, h2⟩
  have hle : KStar.TotallyRealRoots.princ 2 a ≤ H :=
    KStar.TotallyRealRoots.princ_le_of_isClosed (by omega) (fun _ => ha) hH (H.pow_mem hu 2) hem
  have hnot : u ∉ KStar.TotallyRealRoots.princ 2 a := by
    rw [KStar.TotallyRealRoots.mem_princ, hp]
    intro h
    apply h3
    rw [← two_pow_dvd_intCast_padic_iff]
    exact_mod_cast h
  have hidx : (KStar.TotallyRealRoots.princ 2 a).index ≤ Nat.totient (2 ^ a) := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_le_card_group _
  have hpos : 0 < (KStar.TotallyRealRoots.princ 2 a).index := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker]
    exact Nat.card_pos
  have hr := Subgroup.relIndex_mul_index hle
  have hr1 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h hu)
  have hr0 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    omega
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, mul_zero] at hr
    omega
  · calc 2 * H.index ≤ (KStar.TotallyRealRoots.princ 2 a).relIndex H * H.index :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (KStar.TotallyRealRoots.princ 2 a).index := hr
      _ ≤ Nat.totient (2 ^ a) := hidx

theorem UpperTheory.V.Two.idxAdic :
    ∀ (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p c : ℕ), IsClosed (H : Set ℤ_[2]ˣ) → u ∈ H → (u : ℤ_[2]) = p → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → H.index ≠ 0 ∧ H.index ≤ c := by
  intro H u p c hH hu hp hpc
  rcases hpc with ⟨hp8, rfl⟩ | ⟨hp16, rfl⟩
  · have hk : p = 8 * (p / 8) + 3 := by omega
    generalize p / 8 = k at hk
    subst hk
    have e : ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 = 16 * (4 * (k : ℤ) ^ 2 + 3 * k) + 8 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (3 + 1) ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (8 * k + 3) 3 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 3) = 4 := by decide
    omega
  · have hk : p = 16 * (p / 16) + 7 := by omega
    generalize p / 16 = k at hk
    subst hk
    have e : ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 = 32 * (8 * (k : ℤ) ^ 2 + 7 * k + 1) + 16 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (4 + 1) ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (16 * k + 7) 4 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 4) = 8 := by decide
    omega
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.decIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p c : ℕ) (A₀ : ValuationSubring Ω), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → A₀.valuation (p : Ω) < 1 →
      ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≠ 0 ∧ ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≤ c := by
  intro Ω _ _ _ p c A₀ hp hc hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgζ⟩ := decFrob Ω p A₀ hA
  have hodd : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left, Nat.odd_iff]; omega
  have hu : ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = p := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ n)
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val :=
      cyclotomicCharacter.spec 2 (n := n) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
    have h2 := hgζ (2 ^ n) (Nat.Coprime.pow_left n hodd) ζ hζ.pow_eq_one
    rw [h2] at h1
    have h3 : p ≡ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val [MOD 2 ^ n] := by
      have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by positivity)
      rwa [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val]
  have hcl : IsClosed ((decImage ℚ 2 A₀ : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    ((isClosed_Dec (F := ℚ) A₀).isCompact.image (continuous_cycZ ℚ Ω 2)).isClosed
  obtain ⟨h0, hle⟩ := idxAdic (decImage ℚ 2 A₀) (cycZ ℚ Ω 2 g) p c hcl ⟨g, hg, rfl⟩ hu hc
  have e : (cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀ = (decImage ℚ 2 A₀).comap (cycZ ℚ Ω 2) := by
    rw [decImage, Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : (decImage ℚ 2 A₀).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  refine ⟨fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hrel0).trans ?_
  rwa [Subgroup.relIndex_top_right]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.orbTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p c : ℕ), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → OrbLe (cycU 2 (abU Ω (withI M))) p (c * M.deg) := by
  intro Ω _ _ _ M p c hp hc
  classical
  obtain ⟨hsupAb, hdeg, hmem, hcyc⟩ := abBasic Ω
  have hK4 : (cycZ ℚ Ω 2).ker ≤ (galChar Ω 4).ker := (levChar Ω 2 2 ⊤).2
  have hV : cycU 2 (abU Ω (withI M)) = abU Ω M ⊓ (cycZ ℚ Ω 2).ker := by
    show abU Ω (M.sup (AbF.cyc 4)) ⊓ (cycZ ℚ Ω 2).ker = _
    rw [hsupAb, hcyc 4, inf_assoc, inf_eq_right.mpr hK4]
  haveI hWn : (abU Ω M).Normal := by
    haveI : NeZero M.m := ⟨M.pos.ne'⟩
    constructor
    intro g hg h
    rw [hmem M M.m dvd_rfl] at hg ⊢
    have hconj : galChar Ω M.m (h * g * h⁻¹) = galChar Ω M.m g := by
      rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω M.m h), mul_inv_cancel_right]
    rw [hconj]
    exact hg
  rw [hV]
  by_cases hex : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
  · obtain ⟨A₀, hA₀⟩ := hex
    obtain ⟨hKD0, hKDle⟩ := decIndex Ω p c A₀ hp hc hA₀
    have hi : (abU Ω M).index = M.deg := (hdeg M).1
    have hW0 : (abU Ω M).index ≠ 0 := hi ▸ (hdeg M).2.1
    obtain ⟨hne, hle⟩ := supIndex (G ℚ Ω) (cycZ ℚ Ω 2).ker (abU Ω M) (Dec A₀) hW0 hKD0
    obtain ⟨T, hT, h1, h2⟩ := orbIndex Ω p (abU Ω M ⊓ (cycZ ℚ Ω 2).ker) A₀ hp hA₀ hne
    refine ⟨T, hT.trans ?_, h1, h2⟩
    calc _ ≤ (abU Ω M).index * ((cycZ ℚ Ω 2).ker ⊔ Dec A₀).index := hle
      _ ≤ M.deg * c := by rw [hi]; exact Nat.mul_le_mul_left _ hKDle
      _ = c * M.deg := Nat.mul_comm _ _
  · push_neg at hex
    exact ⟨∅, by simp, by simp, fun A hA => absurd hA (not_lt.mpr (hex A))⟩
