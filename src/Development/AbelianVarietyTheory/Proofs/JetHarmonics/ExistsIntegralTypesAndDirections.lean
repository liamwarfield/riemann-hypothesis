module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsUnitSubOfRingHomNe
namespace GlobalTheory

theorem _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ σ σ' : A →+* O, σ ≠ σ' → ∃ a : A, IsUnit (σ a - σ' a) := by
  intro A O _ _ _ _ g hg hgO hA σ σ' hne
  by_contra hcon
  push_neg at hcon
  apply hne
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  set J : Ideal O := Ideal.span ((fun a => σ a - σ' a) '' (s : Set A)) with hJ
  have hmem : ∀ a : A, σ a - σ' a ∈ J := by
    intro a
    have ha : a ∈ Submodule.span ℤ (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
        have : σ (y + z) - σ' (y + z) = (σ y - σ' y) + (σ z - σ' z) := by
          rw [map_add (f := _), map_add (f := _)]; ring
        rw [this]
        exact J.add_mem hy hz
    | smul n y _ hy =>
        have : σ (n • y) - σ' (n • y) = (n : O) * (σ y - σ' y) := by
          simp [zsmul_eq_mul, mul_sub]
        rw [this]
        exact J.mul_mem_left _ hy
  have hgk : (g : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have hle : J ≤ Ideal.span {(g : O)} • J := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨a, -, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA a)
    have hc1 : σ c * g = σ a ^ g - σ a := by
      rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]
    have hc2 : σ' c * g = σ' a ^ g - σ' a := by
      rw [← map_natCast σ' g, ← map_mul, hc, map_sub, map_pow]
    have hgeom := geom_sum₂_mul (σ a) (σ' a) g
    have key : (σ a - σ' a) * ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) =
        (g : O) * (σ c - σ' c) := by
      linear_combination hgeom - hc1 + hc2
    have hr : IsLocalRing.residue O (σ' a) = IsLocalRing.residue O (σ a) := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon a))
    have hS : (∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) ∈
        IsLocalRing.maximalIdeal O := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← IsLocalRing.residue_eq_zero_iff, map_sum]
      simp_rw [map_mul, map_pow, hr, ← pow_add]
      rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue O (σ a) ^ (g - 1))
        (fun i hi => by have := Finset.mem_range.mp hi; congr 1; omega)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hgk, zero_mul]
    have hu : IsUnit ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) := by
      by_contra hu
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
        have := Ideal.sub_mem _ hS
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))
        simpa using this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have : σ a - σ' a = ((g : O) * (σ c - σ' c)) * ↑hu.unit⁻¹ := by
      rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
    show σ a - σ' a ∈ (Ideal.span {(g : O)} • J : Ideal O)
    rw [this, Ideal.smul_eq_mul]
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hmem c))
  have hfg : J.FG := by
    classical
    exact ⟨s.image (fun a => σ a - σ' a), by rw [Finset.coe_image]⟩
  have hjac : Ideal.span {(g : O)} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hspan
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ J hfg hle hjac
  ext a
  have := hmem a
  rw [hbot] at this
  exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HomValueCongruentIntModPrime
namespace GlobalTheory

theorem mem_span_prime_of_not_isUnit_of_pow_sub_mem {O : Type} [CommRing O] [IsLocalRing O] (g : ℕ)
    (hg : g.Prime) (y : O) (hy : y ^ g - y ∈ Ideal.span {(g : O)}) (hn : ¬ IsUnit y) :
    y ∈ Ideal.span {(g : O)} := by
  have hm : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).mpr hn
  have hpos : 1 ≤ g - 1 := by have := hg.two_le; omega
  have hz : y ^ (g - 1) ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp hz)
  have e : y ^ g = y * y ^ (g - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hg.one_lt.le]
  have hy' : y = -(y ^ g - y) * ↑u⁻¹ := by
    calc y = y * (↑u * ↑u⁻¹) := by simp
      _ = -(y ^ g - y) * ↑u⁻¹ := by rw [hu, e]; ring
  rw [hy']
  exact Ideal.mul_mem_right _ _ (neg_mem hy)

theorem hom_value_congruent_int_mod_prime :
    ∀ (A O : Type) [CommRing A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (σ : A →+* O) (x : A), (∃ i : ℤ, σ x - (i : O) ∈ Ideal.span {(g : O)}) ∧ (¬ IsUnit (σ x) → σ x ∈ Ideal.span {(g : O)}) := by
  intro A O _ _ _ g hg hgu hA σ x
  have hy : σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
    have h := Ideal.mem_map_of_mem σ (hA x)
    rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow] at h
    exact h
  refine ⟨?_, fun hn => mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg (σ x) hy hn⟩
  have : Fact g.Prime := ⟨hg⟩
  have : NeZero g := ⟨hg.ne_zero⟩
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hgu
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hgk : ((g : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have : CharP (IsLocalRing.ResidueField O) g := (CharP.charP_iff_prime_eq_zero hg).mpr hgk
  have hfix : IsLocalRing.residue O (σ x) ^ g = IsLocalRing.residue O (σ x) := by
    have h := (IsLocalRing.residue_eq_zero_iff _).mpr (hspan hy)
    rwa [map_sub, map_pow, sub_eq_zero] at h
  obtain ⟨a, ha⟩ : ∃ a : ZMod g,
      IsLocalRing.residue O (σ x) = ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O) a := by
    by_contra hno
    simp only [not_exists] at hno
    classical
    have hpoly : (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero hg.one_lt
    have hnot : IsLocalRing.residue O (σ x) ∉
        Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)) := by
      intro h
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h
      exact hno b hb.symm
    have hsub : (insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)))).val ⊆
        (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)).roots := by
      intro z hz
      have hz' : z ∈ insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O))) := hz
      rw [Polynomial.mem_roots hpoly, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hz' with h | h
      · rw [h]; exact hfix
      · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp h
        rw [← map_pow, ZMod.pow_card]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Polynomial.natDegree_X_pow_sub_X hg.one_lt, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ, ZMod.card] at hcard
    omega
  have ha' : IsLocalRing.residue O (σ x) = IsLocalRing.residue O ((a.val : ℕ) : O) := by
    rw [ha, map_natCast, ← map_natCast (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)),
      ZMod.natCast_zmod_val]
  have hnu : ¬ IsUnit (σ x - ((a.val : ℕ) : O)) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, ha', sub_self]
  have hne : Ideal.span {(g : O)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hgu
  have : Nontrivial (O ⧸ Ideal.span {(g : O)}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : CharP (O ⧸ Ideal.span {(g : O)}) g := (CharP.charP_iff_prime_eq_zero hg).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  have hyQ : Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) ^ g
      - Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) = 0 := by
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hy
  have hnQ : ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) ^ g = ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) := by
    rw [← map_natCast (ZMod.castHom (dvd_refl g) (O ⧸ Ideal.span {(g : O)})), ← map_pow, ZMod.pow_card]
  have hsh : (σ x - ((a.val : ℕ) : O)) ^ g - (σ x - ((a.val : ℕ) : O)) ∈ Ideal.span {(g : O)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_sub, map_natCast, sub_pow_char, hnQ]
    linear_combination hyQ
  refine ⟨(a.val : ℤ), ?_⟩
  rw [Int.cast_natCast]
  exact mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg _ hsh hnu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSeparatingModPrimePow
namespace GlobalTheory

private lemma ringHom_pow_sub_mem_span {A O : Type} [CommRing A] [CommRing O] (g : ℕ)
    (hA : ∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) (σ : A →+* O) (x : A) :
    σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA x)
  exact Ideal.mem_span_singleton'.mpr
    ⟨σ c, by rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]⟩

theorem _root_.GlobalTheory.exists_separating_mod_prime_pow : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (T : Type) [Fintype T] [DecidableEq T] (σ : T → A →+* O), Function.Injective σ → ∀ (K : ℕ) (t₀ : T), ∃ e : A, ∀ t, σ t e - (if t = t₀ then 1 else 0) ∈ Ideal.span {(g : O) ^ K} := by
  intro A O _ _ _ _ g hg hgO hA T _ _ σ hσ K t₀
  have h2 : 2 ≤ g := hg.two_le
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hb : ∀ t, t ≠ t₀ → ∃ b : A, σ t b ∈ Ideal.span {(g : O)} ∧ IsUnit (σ t₀ b) := by
    intro t ht
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne A O g hg hgO hA (σ t₀) (σ t)
      (fun h => ht (hσ h).symm)
    obtain ⟨⟨i, hi⟩, -⟩ := _root_.GlobalTheory.hom_value_congruent_int_mod_prime A O g hg hgO hA (σ t) a
    refine ⟨a - (i : A), by rwa [map_sub, map_intCast], ?_⟩
    rw [map_sub, map_intCast]
    by_contra hn
    have h1 : σ t₀ a - (i : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hn)
    have h3 : σ t₀ a - σ t a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 (hspan hi)
      rwa [sub_sub_sub_cancel_right] at this
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) ha
  choose! b hb1 hb2 using hb
  obtain ⟨c, hc0, hct⟩ : ∃ c : A, IsUnit (σ t₀ c) ∧ ∀ t, t ≠ t₀ → σ t c ∈ Ideal.span {(g : O)} := by
    refine ⟨∏ t ∈ Finset.univ.erase t₀, b t, ?_, fun t ht => ?_⟩
    · rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun t ht => hb2 t (Finset.ne_of_mem_erase ht))
    · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)]
      exact Ideal.mul_mem_right _ _ (hb1 t ht)
  obtain ⟨f, hf0, hft⟩ : ∃ f : A, σ t₀ f - 1 ∈ Ideal.span {(g : O)} ∧
      ∀ t, t ≠ t₀ → σ t f ∈ Ideal.span {(g : O)} := by
    refine ⟨c ^ (g - 1), ?_, fun t ht => ?_⟩
    · rw [map_pow]
      have hz : σ t₀ c * (σ t₀ c ^ (g - 1) - 1) = σ t₀ c ^ g - σ t₀ c := by
        rw [mul_sub, mul_one, ← pow_succ']
        congr 2
        omega
      have : σ t₀ c ^ (g - 1) - 1 = (σ t₀ c ^ g - σ t₀ c) * ↑hc0.unit⁻¹ := by
        rw [← hz, mul_comm (σ t₀ c), mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (ringHom_pow_sub_mem_span g hA (σ t₀) c)
    · rw [map_pow]
      exact Ideal.pow_mem_of_mem _ (hct t ht) _ (by omega)
  refine ⟨1 - (1 - f ^ K) ^ K, fun t => ?_⟩
  rw [← Ideal.span_singleton_pow]
  split_ifs with ht
  · subst ht
    simp only [map_sub, map_one, map_pow]
    have h1 : 1 - σ t f ^ K ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hf0 ⊢
      rw [map_sub, map_one, map_pow]
      rw [map_sub, map_one, sub_eq_zero] at hf0
      rw [hf0, one_pow, sub_self]
    have : 1 - (1 - σ t f ^ K) ^ K - 1 = -((1 - σ t f ^ K) ^ K) := by ring
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow h1 K)
  · simp only [map_sub, map_one, map_pow]
    have hw : σ t f ^ K ∈ Ideal.span {(g : O)} ^ K := Ideal.pow_mem_pow (hft t ht) K
    have hgs := geom_sum_mul (1 - σ t f ^ K) K
    have : 1 - (1 - σ t f ^ K) ^ K - 0 =
        (∑ i ∈ Finset.range K, (1 - σ t f ^ K) ^ i) * σ t f ^ K := by
      linear_combination hgs
    rw [this]
    exact Ideal.mul_mem_left _ _ hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowSubSelfMemSpanOfSplitsCompletely
open NumberField

namespace GlobalTheory

theorem eq_of_le_of_multiset_prod_eq_pow_card {g : ℕ} (hg : 0 < g) (s : Multiset ℕ)
    (hle : ∀ a ∈ s, g ≤ a) (hprod : s.prod = g ^ s.card) : ∀ a ∈ s, a = g := by
  intro a ha
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ht : g ^ t.card ≤ t.prod :=
    Multiset.pow_card_le_prod (fun b hb => hle b (Multiset.mem_cons_of_mem hb))
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ'] at hprod
  have hpos : 0 < g ^ t.card := pow_pos hg _
  have h1 : a * g ^ t.card ≤ g * g ^ t.card := hprod ▸ Nat.mul_le_mul_left a ht
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) (hle a (Multiset.mem_cons_self _ _))

theorem pow_sub_self_mem_span_of_splits_completely (E : Type) [Field E] [NumberField E] (g : ℕ)
    (hg : g.Prime)
    (hcard : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card =
      Module.finrank ℚ E)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup)
    (x : 𝓞 E) : x ^ g - x ∈ Ideal.span {(g : 𝓞 E)} := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have hall : ∀ a ∈ s.map Ideal.absNorm, a = g := by
    refine eq_of_le_of_multiset_prod_eq_pow_card hg.pos _ hle ?_
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map, hcard]
  have hmem : ∀ P ∈ s, x ^ g - x ∈ P := by
    intro P hP
    have hNP : Ideal.absNorm P = g := hall _ (Multiset.mem_map_of_mem _ hP)
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (hprime P hP)
    have hPm : P.IsMaximal := hPp.isMaximal (hprime P hP).ne_zero
    have hc : Nat.card (𝓞 E ⧸ P) = g := by
      rw [← hNP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hfin : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
    let := Fintype.ofFinite (𝓞 E ⧸ P)
    let := Ideal.Quotient.field P
    rw [← Ideal.Quotient.eq, map_pow, ← hc, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hdvd : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) ∣ Ideal.span {x ^ g - x} :=
    Finset.prod_primes_dvd _ hprime fun P hP =>
      Ideal.dvd_span_singleton.mpr (hmem P hP)
  have he : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) = I := by
    rw [← hprod, Finset.prod_mk, Multiset.map_id']
  rw [he] at hdvd
  exact Ideal.dvd_span_singleton.mp hdvd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_lift_ringOfIntegers {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, hf⟩

theorem exists_dual_of_extends {V : Type} [CommRing V] {d r : ℕ} (u : Fin r → Fin d → V)
    (w : Fin d → Fin d → V) (emb : Fin r ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ x : Fin d → V, ∃! a : Fin d → V, ∀ j, ∑ k, a k * w k j = x j) :
    ∃ lam : Fin r → Fin d → V, ∀ i i', ∑ s, lam i s * u i' s = if i = i' then 1 else 0 := by
  have hsurj : Function.Surjective (Matrix.of w).vecMul := by
    intro x
    obtain ⟨a, ha, -⟩ := hb x
    exact ⟨a, funext fun j => by simpa [Matrix.vecMul, dotProduct] using ha j⟩
  have hU : IsUnit (Matrix.of w) := Matrix.vecMul_surjective_iff_isUnit.1 hsurj
  obtain ⟨N, hN⟩ := hU.exists_right_inv
  refine ⟨fun i s => N s (emb i), fun i i' => ?_⟩
  have h := congrFun (congrFun hN (emb i')) (emb i)
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [Matrix.of_apply, hw, EmbeddingLike.apply_eq_iff_eq] at h
  simp only [mul_comm (N _ _), h, eq_comm]

theorem isUnit_Ov_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : TWO.Ov v) :
    IsUnit x ↔ ¬ 0 < v (x : F) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [TWO.v_unit]
    exact lt_irrefl _
  · intro h
    have hx : (x : F) ≠ 0 := by
      intro h0
      apply h
      rw [h0, AddValuation.map_zero]
      exact WithTop.coe_lt_top (0 : ℚ)
    have hi : (x : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v (x : F)) ?_ (not_lt.1 h)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : TWO.Ov v) (Subtype.ext (mul_inv_cancel₀ hx))

theorem exists_integral_types_and_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C ϖ hϖ g hg hgu hcard hnd F _ _ _ _ _ v hv
  letI := io.toAlgebra
  classical
  have hfrob := GlobalTheory.pow_sub_self_mem_span_of_splits_completely E g hg hcard hnd
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ => exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have huv : ∀ ℓ i, C.ch.uvec ℓ i = algebraMap T.V T.Fr (C.uvecT ℓ i) := C.gen.1.2.2.2.2.2.2
  have hact : ∀ a j, C.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (C.actT a j) := C.gen.1.2.1
  have hσinj : Function.Injective σV := by
    intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    have h1 : embK c τ a = embK c τ' a := io.injective (by rw [← hσV', ← hσV', h])
    have h2 := congrArg (fun z : c.F => (z : ℂ)) h1
    exact h2
  let ρ : 𝓞 E → Matrix (Fin (chD C.ch)) (Fin (chD C.ch)) T.V := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a i)
  have hρK : ∀ a i j, dAct T.Fr C.ch.B a i j = algebraMap T.V T.Fr (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    rfl
  have hρF : ∀ a i j, dAct F C.ch.B a i j = algebraMap T.V F (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    exact (IsScalarTower.algebraMap_apply T.V T.Fr F _).symm
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (ρ a).mulVec (C.uvecT ℓ) = σV ℓ.1 a • C.uvecT ℓ := by
    intro a ℓ
    funext i
    apply hinj
    have h := congrFun (GlobalTheory.T.integral_chart_directions_are_eigenvectors E H Dw l Xo c T io y C a ℓ) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρK, huv, ← hσV'] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    exact h
  obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD C.ch) ρ (E →+* ℂ) Dw.mult
    (fun τ a => σV τ a) C.uvecT
    (fun τ τ' hne => GlobalTheory.exists_isUnit_sub_of_ringHom_ne (𝓞 E) T.V g hg hgu hfrob _ _ (fun h => hne (hσinj h)))
    heig (fun τ => by
      obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C τ
      exact exists_dual_of_extends (fun i => C.uvecT ⟨τ, i⟩) w emb hw hb)
  choose ε hε using fun τ => GlobalTheory.exists_separating_mod_prime_pow (𝓞 E) T.V g hg hgu hfrob (E →+* ℂ) σV hσinj 1 τ
  let f : T.V →+* TWO.Ov v := TWO.fO v hϖ hv
  have hf : ∀ x, (f x : F) = algebraMap T.V F x := fun x => (IsScalarTower.algebraMap_apply T.V T.Fr F x).symm
  have hgO : ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
    intro h
    rw [← map_natCast f] at h
    exact hgu ((isUnit_map_iff f _).1 h)
  refine ⟨fun τ => f.comp (σV τ), fun ℓ i => f (C.uvecT ℓ i), fun τ a => ?_, fun ℓ i => hf _, fun ℓ i => ?_,
    fun a ℓ => ?_, fun τ a => ⟨fun h => ?_, fun h => (isUnit_Ov_iff v _).2 h⟩, fun τ a => ?_,
    ⟨fun ℓ s => f (lam ℓ s), fun ℓ ℓ' => ?_⟩, ⟨ε, fun τ τ' => ?_⟩, hgO⟩
  · rw [RingHom.comp_apply, hf, ← hσV', ← IsScalarTower.algebraMap_apply]
  · rw [hf, huv, ← IsScalarTower.algebraMap_apply]
  · funext i
    have h := congrArg (algebraMap T.V F) (congrFun (heig a ℓ) i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρF, hf, RingHom.comp_apply]
    exact h
  · exact (GlobalTheory.hom_value_congruent_int_mod_prime (𝓞 E) (TWO.Ov v) g hg hgO hfrob _ a).2
      (fun hu => (isUnit_Ov_iff v _).1 hu h)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    have h2 : σV (ComplexEmbedding.conjugate τ) a = σV τ (H.bar a) := hinj (by rw [hσV', hσV', h])
    exact congrArg f h2
  · have h := congrArg f (hlam ℓ ℓ')
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul] at h
    rw [h]
    by_cases hl : ℓ = ℓ'
    · rw [if_pos hl, if_pos hl, map_one]
    · rw [if_neg hl, if_neg hl, map_zero]
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hε τ τ')
    refine Ideal.mem_span_singleton'.2 ⟨f b, ?_⟩
    have h := congrArg f hb
    rw [pow_one, map_mul, map_natCast, map_sub] at h
    rw [h, RingHom.comp_apply]
    by_cases ht : τ = τ'
    · rw [if_pos ht, if_pos ht.symm, map_one]
    · rw [if_neg ht, if_neg (Ne.symm ht), map_zero]

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
end
