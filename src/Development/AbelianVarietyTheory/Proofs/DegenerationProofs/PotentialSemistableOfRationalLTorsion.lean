module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightLeAddOfTorsionPairing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompositumFiniteNormalIsPGroup
namespace GlobalTheory

open IntermediateField Polynomial

theorem compositum_finite_normal_isPGroup (K K' Ω : Type) [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ)
    (L : IntermediateField K Ω) (hfin : FiniteDimensional K L) (hn : Normal K L)
    (hp : IsPGroup l (L ≃ₐ[K] L)) :
    FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K']
        IntermediateField.adjoin K' (L : Set Ω)) := by
  obtain ⟨p, hsp⟩ := Normal.exists_isSplittingField K L
  obtain ⟨hs, hL⟩ := IntermediateField.isSplittingField_iff.mp hsp
  have hsΩ : (p.map (algebraMap K Ω)).Splits := by
    have := hs.map (algebraMap L Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hmm : (p.map (algebraMap K K')).map (algebraMap K' Ω) = p.map (algebraMap K Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : (p.map (algebraMap K K')).rootSet Ω = p.rootSet Ω := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmm]
  have hE : IntermediateField.adjoin K' (L : Set Ω) =
      IntermediateField.adjoin K' ((p.map (algebraMap K K')).rootSet Ω) := by
    rw [hroot]
    conv_lhs => rw [hL]
    exact IntermediateField.adjoin_adjoin_right _ _
  have hsp' : (p.map (algebraMap K K')).IsSplittingField K'
      (IntermediateField.adjoin K' (L : Set Ω)) := by
    rw [hE]
    exact IntermediateField.adjoin_rootSet_isSplittingField (by rw [hmm]; exact hsΩ)
  refine ⟨Polynomial.IsSplittingField.finiteDimensional _ (p.map (algebraMap K K')),
    Normal.of_isSplittingField (p.map (algebraMap K K')), ?_⟩
  set E := IntermediateField.adjoin K' (L : Set Ω) with hEdef
  let i : L →ₐ[K] E :=
    { toFun := fun x => ⟨x, IntermediateField.subset_adjoin K' _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI : Algebra L E := i.toRingHom.toAlgebra
  haveI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  let r : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E) :=
    { toFun := fun g => g.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : (E ≃ₐ[K'] E) →* (L ≃ₐ[K] L) := (AlgEquiv.restrictNormalHom L).comp r
  refine hp.of_injective φ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : L, g (i x) = i x := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (r g) L x
    have h2 : (r g).restrictNormal L = 1 := hg
    rw [h2] at h1
    exact h1.symm
  have : (g : E →ₐ[K'] E) = AlgHom.id K' E :=
    IntermediateField.adjoin_algHom_ext K' fun x hx => hfix ⟨x, hx⟩
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun this x)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KummerTwistRelationAndFixedField
namespace GlobalTheory

private theorem pow_apply_eq_pow_mul_of_apply_eq_mul {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (hζ : ζ ∈ Set.range (algebraMap F Ω))
    (hσ : σ ρ = ζ * ρ) (k : ℕ) : (σ ^ k) ρ = ζ ^ k * ρ := by
  obtain ⟨z, rfl⟩ := hζ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hσ, map_mul, AlgEquiv.commutes, ih]
    ring

private theorem sum_pow_apply_pow_mem_bot_of_kummer {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (n : ℕ) (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (c : F) (hρ : ρ ^ n = algebraMap F Ω c)
    (hζ : IsPrimitiveRoot ζ n) (hζF : ζ ∈ Set.range (algebraMap F Ω)) (hσ : σ ρ = ζ * ρ)
    (i : ℕ) : ∑ k ∈ Finset.range n, (σ ^ k) (ρ ^ i) ∈ (⊥ : Subalgebra F Ω) := by
  have hk : ∀ k, (σ ^ k) (ρ ^ i) = (ζ ^ i) ^ k * ρ ^ i := by
    intro k
    rw [map_pow, pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ k]
    ring
  simp_rw [hk, ← Finset.sum_mul]
  by_cases h1 : ζ ^ i = 1
  · rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    obtain ⟨m, rfl⟩ := (hζ.pow_eq_one_iff_dvd i).1 h1
    rw [pow_mul, hρ, ← map_pow, ← map_natCast (algebraMap F Ω) n, ← map_mul]
    exact Subalgebra.algebraMap_mem _ _
  · rw [geom_sum_eq h1, ← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div, zero_mul]
    exact Subalgebra.zero_mem _

theorem kummer_twist_relation_and_fixed_field :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n q : ℕ) (ρ ζ : Ω) (c : F) (σ : Ω ≃ₐ[F] Ω) (φ : Ω →+* Ω), 0 < n → ρ ^ n = algebraMap F Ω c → φ (algebraMap F Ω c) = algebraMap F Ω c → (∀ a : F, φ (algebraMap F Ω a) ∈ Set.range (algebraMap F Ω)) → (∀ ξ : Ω, ξ ^ n = 1 → ξ ∈ Set.range (algebraMap F Ω)) → IsPrimitiveRoot ζ n → σ ρ = ζ * ρ → φ ζ = ζ ^ q → ∀ x ∈ IntermediateField.adjoin F ({ρ} : Set Ω), φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ Set.range (algebraMap F Ω)) := by
  intro F Ω _ _ _ _ n q ρ ζ c σ φ hn hρ hφc hφF hroots hζ hσ hφζ x hx
  have hζF : ζ ∈ Set.range (algebraMap F Ω) := hroots ζ hζ.pow_eq_one
  refine ⟨?_, fun hsx => ?_⟩
  ·
    have hρ' : φ (σ ρ) = (σ ^ q) (φ ρ) := by
      by_cases h0 : ρ = 0
      · simp [h0]
      · have hc : algebraMap F Ω c ≠ 0 := by rw [← hρ]; exact pow_ne_zero _ h0

        have hξ : (φ ρ / ρ) ^ n = 1 := by
          rw [div_pow, ← map_pow, hρ, hφc, div_self hc]
        obtain ⟨e, he⟩ := hroots _ hξ
        have hφρ : φ ρ = algebraMap F Ω e * ρ := by rw [he, div_mul_cancel₀ _ h0]
        rw [hσ, map_mul, hφζ, hφρ, map_mul, AlgEquiv.commutes,
          pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ q]
        ring
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hρ'
    | algebraMap a =>
      obtain ⟨b, hb⟩ := hφF a
      rw [AlgEquiv.commutes, ← hb]
      exact ((σ ^ q).commutes b).symm
    | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
    | inv y _ hy => simp only [map_inv₀, hy]
    | mul y z _ _ hy hz => simp only [map_mul, hy, hz]
  ·
    have halg : IsAlgebraic F ρ :=
      ⟨Polynomial.X ^ n - Polynomial.C c, (Polynomial.monic_X_pow_sub_C c hn.ne').ne_zero,
        by simp [hρ]⟩
    have hx' : x ∈ Algebra.adjoin F {ρ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
      exact (IntermediateField.mem_toSubalgebra _ _).2 hx
    have havg : ∀ y ∈ Algebra.adjoin F {ρ},
        ∑ k ∈ Finset.range n, (σ ^ k) y ∈ (⊥ : Subalgebra F Ω) := by
      intro y hy
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [Polynomial.aeval_eq_sum_range]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [map_sum, map_smul]
      rw [Finset.sum_comm]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      rw [← Finset.smul_sum]
      exact Subalgebra.smul_mem _
        (sum_pow_apply_pow_mem_bot_of_kummer n σ ρ ζ c hρ hζ hζF hσ i) _
    have hall : ∀ k : ℕ, (σ ^ k) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hsx, ih]
    have hsum := havg x hx'
    simp_rw [hall, Finset.sum_const, Finset.card_range] at hsum
    obtain ⟨b, hb⟩ := Algebra.mem_bot.1 hsum
    have hn0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hn0' : (n : Ω) ≠ 0 := by
      rw [← map_natCast (algebraMap F Ω) n]; exact (map_ne_zero _).2 hn0
    refine ⟨b / n, ?_⟩
    rw [map_div₀, hb, map_natCast, nsmul_eq_mul]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
namespace GlobalTheory.SS.MaxUnr
open IsLocalRing Polynomial

theorem pow_pow_mul_eq {M : Type*} [Monoid M] {q f : ℕ} {x : M} (h : x ^ q ^ f = x) (g : ℕ) :
    x ^ q ^ (f * g) = x := by
  induction g with
  | zero => simp
  | succ g ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

def Teich (q : ℕ) (S : Type*) [Monoid S] : Set S := {t | ∃ f, 1 ≤ f ∧ t ^ q ^ f = t}

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem one_lt_card [Finite (ResidueField V)] : 1 < Nat.card (ResidueField V) :=
  Finite.one_lt_card

theorem isIntegral_of_teich {q : ℕ} (hq : 1 < q) {S : Type*} [CommRing S] [Algebra V S] {t : S}
    (ht : t ∈ Teich q S) : IsIntegral V t := by
  obtain ⟨f, hf, h⟩ := ht
  refine ⟨X ^ q ^ f - X, monic_X_pow_sub ?_, by simp [h]⟩
  refine lt_of_le_of_lt degree_X_le ?_
  exact_mod_cast Nat.one_lt_pow (by omega) hq

theorem isLocalRing_of_isIntegral [IsAdicComplete (maximalIdeal V) V] (S : Type*) [CommRing S]
    [IsDomain S] [Algebra V S] [Algebra.IsIntegral V S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite V (Algebra.adjoin V {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) (Algebra.adjoin V {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton V a⟩ : Algebra.adjoin V {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin V {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin V {a}).val)

theorem isLocalHom_of_injective {S S' : Type*} [CommRing S] [CommRing S'] [Algebra V S] [Algebra V S']
    [Algebra.IsIntegral V S'] (g : S →ₐ[V] S') (hg : Function.Injective g) :
    IsLocalHom g.toRingHom := by
  refine RingHom.IsIntegral.isLocalHom (fun x => ?_) hg
  let := g.toRingHom.toAlgebra
  have : IsScalarTower V S S' := .of_algebraMap_eq fun v => (g.commutes v).symm
  exact (Algebra.IsIntegral.isIntegral (R := V) x).tower_top (A := S)

theorem exists_prime [Finite (ResidueField V)] : ∃ p n : ℕ, p.Prime ∧ (p : V) ∈ maximalIdeal V ∧
    Nat.card (ResidueField V) = p ^ n := by
  have := Fintype.ofFinite (ResidueField V)
  obtain ⟨p, hp, n, hp', h⟩ := FiniteField.card' (ResidueField V)
  refine ⟨p, n, hp', ?_, by rw [Nat.card_eq_fintype_card, h]⟩
  rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

theorem pow_card_sub_mem [Finite (ResidueField V)] (v : V) :
    v ^ Nat.card (ResidueField V) - v ∈ maximalIdeal V := by
  have := Fintype.ofFinite (ResidueField V)
  rw [← residue_eq_zero_iff, map_sub, map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

theorem teich_of_mem_adjoin [Finite (ResidueField V)] {Q : Type*} [CommRing Q] [Algebra V Q]
    (h0 : ∀ v ∈ maximalIdeal V, algebraMap V Q v = 0) {x : Q}
    (hx : x ∈ Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Q)) :
    x ∈ Teich (Nat.card (ResidueField V)) Q := by
  rcases subsingleton_or_nontrivial Q with _ | _
  · exact ⟨1, le_rfl, Subsingleton.elim _ _⟩
  obtain ⟨p, n, hp, hpm, hq⟩ := exists_prime (V := V)
  have := Fact.mk hp
  have : CharP Q p := (CharP.charP_iff_prime_eq_zero hp).2 (by simpa using h0 _ hpm)
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap v =>
    refine ⟨1, le_rfl, ?_⟩
    have := h0 _ (pow_card_sub_mem v)
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [pow_one, this]
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have h1 := pow_pow_mul_eq hx g
    have h2 := pow_pow_mul_eq hy f
    rw [mul_comm] at h2
    rw [hq, ← pow_mul] at h1 h2 ⊢
    rw [add_pow_char_pow, h1, h2]
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have h2 := pow_pow_mul_eq hy f
    rw [mul_comm] at h2
    rw [mul_pow, pow_pow_mul_eq hx g, h2]

theorem isIntegral_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) : Algebra.IsIntegral V S := by
  refine ⟨fun x => ?_⟩
  have : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) ≤ integralClosure V S :=
    Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  exact this (hS ▸ Algebra.mem_top)

theorem teich_quot_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) (I : Ideal S)
    (hI : (maximalIdeal V).map (algebraMap V S) ≤ I) (x : S ⧸ I) :
    x ∈ Teich (Nat.card (ResidueField V)) (S ⧸ I) := by
  refine teich_of_mem_adjoin (fun v hv => ?_) ?_
  · exact Ideal.Quotient.eq_zero_iff_mem.2 (hI (Ideal.mem_map_of_mem _ hv))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx : x ∈ Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) := hS ▸ Algebra.mem_top
  have h2 := Subalgebra.mem_map.2 ⟨x, hx, (rfl : Ideal.Quotient.mkₐ V I x = _)⟩
  rw [AlgHom.map_adjoin] at h2
  refine Algebra.adjoin_mono ?_ h2
  rintro _ ⟨t, ⟨f, hf, ht⟩, rfl⟩
  exact ⟨f, hf, by rw [← map_pow, ht]⟩

theorem maximalIdeal_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    [IsLocalRing S] [IsLocalHom (algebraMap V S)]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    (maximalIdeal V).map (algebraMap V S) = maximalIdeal S := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit _ v hv) fun x hx => ?_
  obtain ⟨f, hf, h⟩ := teich_quot_of_gen hS _ le_rfl (Ideal.Quotient.mk _ x)
  rw [← map_pow, Ideal.Quotient.eq] at h
  obtain ⟨N, hN⟩ : ∃ N, Nat.card (ResidueField V) ^ f = N + 2 :=
    Nat.exists_eq_add_of_le' (Nat.one_lt_pow (by omega) one_lt_card)
  have hu : IsUnit (1 - x ^ (N + 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem (maximalIdeal S) hx _ (by omega))
  rw [← Ideal.unit_mul_mem_iff_mem _ hu]
  have e : (1 - x ^ (N + 1)) * x = -(x ^ (N + 2) - x) := by ring
  rw [e, ← hN]
  exact neg_mem h

theorem gen_adjoin {q : ℕ} {S : Type*} [CommRing S] [Algebra V S] {T : Set S} (hT : T ⊆ Teich q S) :
    Algebra.adjoin V (Teich q (Algebra.adjoin V T)) = ⊤ := by
  rw [eq_top_iff, ← Algebra.adjoin_adjoin_coe_preimage (R := V) (s := T)]
  refine Algebra.adjoin_mono fun t ht => ?_
  obtain ⟨f, hf, h⟩ := hT ht
  exact ⟨f, hf, Subtype.ext h⟩

theorem dvr_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [IsDomain S] [Algebra V S]
    [FaithfulSMul V S] [IsLocalRing S] [Module.Finite V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    IsDiscreteValuationRing S := by
  have : IsLocalHom (algebraMap V S) :=
    isLocalHom_of_injective (Algebra.ofId V S) (FaithfulSMul.algebraMap_injective V S)
  have : IsNoetherianRing S := IsNoetherianRing.of_finite V S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm := maximalIdeal_of_gen hS
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, ← hm, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective V S)]
    exact hπ.ne_zero
  exact ((IsDiscreteValuationRing.TFAE S hnf).out 1 5).2 (show (maximalIdeal S).IsPrincipal from ⟨⟨_, hm.symm⟩⟩)
end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] [Finite (ResidueField V)]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Finite (ResidueField V)] in
theorem exists_level {q : ℕ} {S : Type*} [CommRing S] [Algebra V S] {x : S}
    (hx : x ∈ Algebra.adjoin V (Teich q S)) :
    ∃ f, 1 ≤ f ∧ ∀ g, x ∈ Algebra.adjoin V {t : S | t ^ q ^ (f * g) = t} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨f, hf, h⟩ := hx
    exact ⟨f, hf, fun g => Algebra.subset_adjoin (pow_pow_mul_eq h g)⟩
  | algebraMap v => exact ⟨1, le_rfl, fun g => Subalgebra.algebraMap_mem _ v⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, fun k => add_mem ?_ ?_⟩
    · rw [mul_assoc]; exact hx _
    · rw [mul_comm f g, mul_assoc]; exact hy _
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, fun k => mul_mem ?_ ?_⟩
    · rw [mul_assoc]; exact hx _
    · rw [mul_comm f g, mul_assoc]; exact hy _

theorem exists_stage {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) (s : Finset S) :
    ∃ (W : Subalgebra V S) (_ : IsDiscreteValuationRing W), (↑s : Set S) ⊆ W ∧
      IsAdicComplete (maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧
      (maximalIdeal V).map (algebraMap V W) = maximalIdeal W ∧
      ∃ f, 1 ≤ f ∧ W = Algebra.adjoin V {t : S | t ^ Nat.card (ResidueField V) ^ f = t} := by
  classical
  set q := Nat.card (ResidueField V) with hq
  have hI := isIntegral_of_gen hS
  choose F hF hF' using fun x : S => exists_level (V := V) (q := q) (x := x) (hS ▸ Algebra.mem_top)
  have hf : 1 ≤ ∏ x ∈ s, F x := Finset.one_le_prod' fun x _ => hF x
  set f := ∏ x ∈ s, F x with hfdef
  have hT : {t : S | t ^ q ^ f = t} ⊆ Teich q S := fun t ht => ⟨f, hf, ht⟩
  have hfin : {t : S | t ^ q ^ f = t}.Finite := by
    have hm : (X ^ q ^ f - X : S[X]).Monic := by
      refine monic_X_pow_sub (lt_of_le_of_lt degree_X_le ?_)
      exact_mod_cast Nat.one_lt_pow (by omega) (one_lt_card (V := V))
    refine (X ^ q ^ f - X : S[X]).roots.finite_toSet.subset fun t ht => ?_
    have ht' : t ^ q ^ f = t := ht
    simp [mem_roots hm.ne_zero, ht']
  set W := Algebra.adjoin V {t : S | t ^ q ^ f = t} with hW
  have hWfin : Module.Finite V W :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hfin fun x _ => Algebra.IsIntegral.isIntegral x
  have hloc : IsLocalRing W := isLocalRing_of_isIntegral (V := V) W
  have hg : Algebra.adjoin V (Teich q W) = ⊤ := gen_adjoin hT
  have hfa : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun a b h =>
    FaithfulSMul.algebraMap_injective V S (congrArg Subtype.val h)
  have : IsLocalHom (algebraMap V W) :=
    isLocalHom_of_injective (Algebra.ofId V W) (FaithfulSMul.algebraMap_injective V W)
  have hm := maximalIdeal_of_gen hg
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
  rw [hm] at hc
  refine ⟨W, dvr_of_gen hg, fun x hx => ?_, hc, hWfin,
    isLocalHom_of_injective W.val Subtype.val_injective, hm, f, hf, rfl⟩
  obtain ⟨g, hg⟩ : F x ∣ f := Finset.dvd_prod_of_mem F hx
  rw [hW, hg]
  exact hF' x g

theorem irreducible_of_gen {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) {π : V} (hπ : Irreducible π) :
    Irreducible (algebraMap V S π) := by
  have hI := isIntegral_of_gen hS
  have hloc : IsLocalRing S := isLocalRing_of_isIntegral (V := V) S
  have : IsLocalHom (algebraMap V S) :=
    isLocalHom_of_injective (Algebra.ofId V S) (FaithfulSMul.algebraMap_injective V S)
  have hm := maximalIdeal_of_gen hS
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have h0 : algebraMap V S π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective V S)]
    exact hπ.ne_zero
  refine Prime.irreducible ((Ideal.span_singleton_prime h0).1 ?_)
  rw [hm]; infer_instance

theorem dvr_of_gen' {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    IsDiscreteValuationRing S := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_of_gen hS hπ, fun {x} hx => ?_⟩
  obtain ⟨W, _, hs, -, -, -, hm, -⟩ := exists_stage hS {x}
  have hxW : x ∈ W := hs (by simp)
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have hi : Irreducible (algebraMap V W π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm.symm
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (x := (⟨x, hxW⟩ : W))
    (fun h => hx (congrArg Subtype.val h)) hi
  exact ⟨n, by simpa using (hn.map W.val).symm⟩

theorem henselian_of_gen {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    HenselianLocalRing S := by
  classical
  have hI := isIntegral_of_gen hS
  have hloc : IsLocalRing S := isLocalRing_of_isIntegral (V := V) S
  refine ⟨fun P hP a h1 h2 => ?_⟩
  obtain ⟨W, _, hs, hc, -, hl, -⟩ := exists_stage hS (insert a P.coeffs)
  have haW : a ∈ W := hs (by simp)
  have hH := GlobalTheory.henselianLocalRing_of_isAdicComplete W
  have hlift : P ∈ lifts W.val.toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases h : P.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨⟨P.coeff n, hs (by simp [coeff_mem_coeffs h])⟩, rfl⟩
  obtain ⟨P', rfl, -, hP'⟩ := lifts_and_natDegree_eq_and_monic hlift hP
  have e : ∀ Q : W[X], (Q.map W.val.toRingHom).eval a = W.val.toRingHom (Q.eval ⟨a, haW⟩) := fun Q =>
    eval_map_apply (p := Q) W.val.toRingHom ⟨a, haW⟩
  rw [derivative_map, e] at h2
  rw [e] at h1
  obtain ⟨b, hb, hb'⟩ := HenselianLocalRing.is_henselian P' hP' ⟨a, haW⟩
    (fun h => h1 (h.map _)) (isUnit_of_map_unit _ _ h2)
  exact ⟨b, hb.map (f := W.val.toRingHom), map_nonunit W.val.toRingHom _ hb'⟩
end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Finite (ResidueField V)]

theorem teich_inj {S : Type*} [CommRing S] [IsLocalRing S] [Algebra V S] [IsLocalHom (algebraMap V S)]
    {t u : S} (ht : t ∈ Teich (Nat.card (ResidueField V)) S)
    (hu : u ∈ Teich (Nat.card (ResidueField V)) S) (h : t - u ∈ maximalIdeal S) : t = u := by
  obtain ⟨f, hf, ht⟩ := ht
  obtain ⟨g, hg, hu⟩ := hu
  have h1 := pow_pow_mul_eq ht g
  have h2 := pow_pow_mul_eq hu f
  rw [mul_comm] at h2
  obtain ⟨p, n, hp, hpm, hq⟩ := exists_prime (V := V)
  have hN : ((Nat.card (ResidueField V) ^ (f * g) : ℕ) : ResidueField S) = 0 := by
    have hp0 : (p : ResidueField S) = 0 := by
      have : residue S (algebraMap V S p) = 0 := (residue_eq_zero_iff _).2 (map_nonunit _ _ hpm)
      simpa using this
    have hn : n ≠ 0 := by
      rintro rfl
      have := one_lt_card (V := V)
      simp [hq] at this
    have := Nat.mul_pos hf hg
    rw [hq, ← pow_mul, Nat.cast_pow, hp0, zero_pow (by positivity)]
  generalize Nat.card (ResidueField V) ^ (f * g) = N at h1 h2 hN
  have h3 := geom_sum₂_mul t u N
  rw [h1, h2] at h3
  have h4 : (∑ i ∈ Finset.range N, t ^ i * u ^ (N - 1 - i)) ∈ maximalIdeal S := by
    have h5 : residue S t = residue S u := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_eq_zero_iff, map_sum]
    simp only [map_mul, map_pow, h5]
    rw [geom_sum₂_self, hN, zero_mul]
  have h6 := isUnit_one_sub_self_of_mem_nonunits _ h4
  rw [← sub_eq_zero, ← h6.mul_right_eq_zero, sub_mul, h3, one_mul, sub_self]

theorem residue_teich {S : Type*} [CommRing S] [IsLocalRing S] [Algebra V S]
    [IsLocalHom (algebraMap V S)] [Algebra.IsIntegral V S] (a : S) :
    ∃ f, 1 ≤ f ∧ a ^ Nat.card (ResidueField V) ^ f - a ∈ maximalIdeal S := by
  have hc : IsIntegral (ResidueField V) (residue S a) := by
    have : IsIntegral V (residue S a) :=
      (Algebra.IsIntegral.isIntegral (R := V) a).map (IsScalarTower.toAlgHom V S (ResidueField S))
    exact this.tower_top
  let F := IntermediateField.adjoin (ResidueField V) {residue S a}
  have : FiniteDimensional (ResidueField V) F := IntermediateField.adjoin.finiteDimensional hc
  have : Finite F := Module.finite_of_finite (ResidueField V)
  have := Fintype.ofFinite F
  refine ⟨Module.finrank (ResidueField V) F, Module.finrank_pos, ?_⟩
  have h := FiniteField.pow_card (⟨_, IntermediateField.mem_adjoin_simple_self _ _⟩ : F)
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ResidueField V)] at h
  rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero]
  exact congrArg Subtype.val h

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra V Ω] [FaithfulSMul V Ω]

omit [IsDomain V] [IsDiscreteValuationRing V] [Finite (ResidueField V)] [IsAlgClosed Ω] in
theorem faithful_sub (R : Subalgebra V Ω) : FaithfulSMul V R :=
  (faithfulSMul_iff_algebraMap_injective V R).2 fun _ _ h =>
    FaithfulSMul.algebraMap_injective V Ω (congrArg Subtype.val h)

theorem exists_teich [IsLocalRing (integralClosure V Ω)] (a : integralClosure V Ω) :
    ∃ t ∈ Teich (Nat.card (ResidueField V)) (integralClosure V Ω),
      a - t ∈ maximalIdeal (integralClosure V Ω) := by
  have := faithful_sub (integralClosure V Ω)
  have : IsLocalHom (algebraMap V (integralClosure V Ω)) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  obtain ⟨f, hf, h⟩ := residue_teich (V := V) a
  set q := Nat.card (ResidueField V) with hq
  have hm : (X ^ q ^ f - X : (integralClosure V Ω)[X]).Monic := by
    refine monic_X_pow_sub (lt_of_le_of_lt degree_X_le ?_)
    exact_mod_cast Nat.one_lt_pow (by omega) (one_lt_card (V := V))
  have hs : (X ^ q ^ f - X : (integralClosure V Ω)[X]).Splits := by
    refine Polynomial.Splits.of_splits_map_of_injective (i := (integralClosure V Ω).val.toRingHom)
      Subtype.val_injective (IsAlgClosed.splits _) fun b hb => ?_
    have hb' := isRoot_of_mem_roots hb
    have : b ∈ Teich q Ω := ⟨f, hf, by simpa [sub_eq_zero] using hb'⟩
    exact ⟨⟨b, isIntegral_of_teich one_lt_card this⟩, rfl⟩
  have h1 : (X ^ q ^ f - X : (integralClosure V Ω)[X]).eval a ∈ maximalIdeal (integralClosure V Ω) := by
    simpa using h
  rw [hs.eval_eq_prod_roots_of_monic hm] at h1
  obtain ⟨c, hc, hcm⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem inferInstance _).1 h1
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hc
  exact ⟨t, ⟨f, hf, by simpa [sub_eq_zero] using isRoot_of_mem_roots ht⟩, hcm⟩

theorem isAlgClosed_residue [IsLocalRing (integralClosure V Ω)]
    [IsLocalRing (Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω))] :
    IsAlgClosed (ResidueField (Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω))) := by
  set R := Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω) with hR
  have hRI : Algebra.IsIntegral V R := isIntegral_of_gen (gen_adjoin subset_rfl)
  have hle : R ≤ integralClosure V Ω := Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  refine IsAlgClosed.of_exists_root _ fun p hp hi => ?_
  obtain ⟨P, hP, hd, hPm⟩ := lifts_and_natDegree_eq_and_monic (f := residue R)
    (p := p) (map_surjective _ residue_surjective _) hp
  have hdeg : P.degree ≠ 0 := by
    have := hi.natDegree_pos
    exact (natDegree_pos_iff_degree_pos.1 (by omega)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective Ω (R := R) Subtype.val_injective P hdeg
  have hαi : IsIntegral V α := isIntegral_trans (A := R) α ⟨P, hPm, hα⟩
  obtain ⟨t, ⟨f, hf, ht⟩, hαt⟩ := exists_teich (⟨α, hαi⟩ : integralClosure V Ω)
  let t' : R := ⟨t, Algebra.subset_adjoin ⟨f, hf, congrArg Subtype.val ht⟩⟩
  let ι : R →+* integralClosure V Ω := (Subalgebra.inclusion hle).toRingHom
  refine ⟨residue R t', ?_⟩
  rw [← hP, eval_map_apply, residue_eq_zero_iff]
  have h0 : (P.map ι).eval ⟨α, hαi⟩ = 0 := by
    apply Subtype.val_injective
    have := eval_map_apply (p := P.map ι) (integralClosure V Ω).val.toRingHom ⟨α, hαi⟩
    refine this.symm.trans ?_
    rw [Polynomial.map_map, eval_map]
    exact hα
  have h1 := Ideal.mem_of_dvd _ (sub_dvd_eval_sub _ _ (P.map ι)) hαt
  rw [h0, zero_sub, neg_mem_iff, show t = ι t' from rfl, eval_map_apply] at h1
  exact fun hu => h1 (hu.map ι)
end

theorem exists_fractionField {V : Type} (K : Type) {Ω : Type} (R : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Field Ω] [Algebra K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [CommRing R] [IsDomain R] [Algebra V R]
    [Algebra R Ω] [IsScalarTower V R Ω] [FaithfulSMul V R] [FaithfulSMul R Ω] :
    ∃ (F : Type) (_ : Field F) (_ : Algebra R F) (_ : IsFractionRing R F) (_ : Algebra F Ω)
      (_ : Algebra K F), IsScalarTower R F Ω ∧ IsScalarTower K F Ω := by
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have hinj : Function.Injective ((algebraMap R F).comp (algebraMap V R)) :=
    (IsFractionRing.injective R F).comp (FaithfulSMul.algebraMap_injective V R)
  let _ : Algebra K F := (IsFractionRing.lift hinj).toAlgebra
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ?_⟩
  refine .of_algebraMap_eq' (IsFractionRing.ringHom_ext (A := V) fun v => ?_)
  have e : algebraMap K F (algebraMap V K v) = algebraMap R F (algebraMap V R v) :=
    IsFractionRing.lift_algebraMap hinj v
  rw [RingHom.comp_apply, e, ← IsScalarTower.algebraMap_apply R F Ω,
    ← IsScalarTower.algebraMap_apply V K Ω, ← IsScalarTower.algebraMap_apply V R Ω]

open GlobalTheory.SS in
theorem main_of (hT : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [CharZero K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (l : ℕ), l.Prime → IsUnit (l : R) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∃ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) ∧ L ≤ IntermediateField.adjoin K {ρ}) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Set.range (algebraMap K Ω)) ∧ ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ) (hA : ∀ (K K' Ω : Type) [Field K] [Field K'] [Field Ω] [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ) (L : IntermediateField K Ω), FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧ Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧ IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K'] IntermediateField.adjoin K' (L : Set Ω))) (hB : ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n q : ℕ) (ρ ζ : Ω) (c : F) (σ : Ω ≃ₐ[F] Ω) (φ : Ω →+* Ω), 0 < n → ρ ^ n = algebraMap F Ω c → φ (algebraMap F Ω c) = algebraMap F Ω c → (∀ a : F, φ (algebraMap F Ω a) ∈ Set.range (algebraMap F Ω)) → (∀ ξ : Ω, ξ ^ n = 1 → ξ ∈ Set.range (algebraMap F Ω)) → IsPrimitiveRoot ζ n → σ ρ = ζ * ρ → φ ζ = ζ ^ q → ∀ x ∈ IntermediateField.adjoin F ({ρ} : Set Ω), φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ Set.range (algebraMap F Ω))) (hC : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)], ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω)) :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl hlu Ω _ _ _ _ _ q hq
  subst hq
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 (by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K))
  have hAloc : IsLocalRing (integralClosure V Ω) := isLocalRing_of_isIntegral (V := V) _
  obtain ⟨φ, hφ⟩ := hC V K hfin Ω
  set q := Nat.card (ResidueField V) with hq
  have hres := @isAlgClosed_residue V _ _ _ _ Ω _ _ _ _ _
  rw [← hq] at hres
  set R := Algebra.adjoin V (Teich q Ω) with hR
  have hg : Algebra.adjoin V (Teich q R) = ⊤ := gen_adjoin subset_rfl
  have hRI : Algebra.IsIntegral V R := isIntegral_of_gen hg
  have hle : R ≤ integralClosure V Ω := Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  have := faithful_sub R
  have := faithful_sub (integralClosure V Ω)
  have hRloc : IsLocalRing R := isLocalRing_of_isIntegral (V := V) _
  have hVR : IsLocalHom (algebraMap V R) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  have hVA : IsLocalHom (algebraMap V (integralClosure V Ω)) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  have hSH : SH R (FractionRing R) := ⟨dvr_of_gen' hg, henselian_of_gen hg, hres, inferInstance⟩
  have hφV : ∀ v : V, φ (algebraMap V Ω v) = algebraMap V Ω v := fun v => by
    rw [IsScalarTower.algebraMap_apply V K Ω, AlgEquiv.commutes]
  have hφT : ∀ t ∈ Teich q Ω, φ t = t ^ q := by
    rintro t ⟨f, hf, ht⟩
    obtain ⟨y, hy, hy'⟩ := hφ ⟨t, isIntegral_of_teich one_lt_card ⟨f, hf, ht⟩⟩
    have := teich_inj (V := V) ⟨f, hf, Subtype.ext (by
        rw [Subalgebra.coe_pow, hy, ← map_pow]; exact congrArg φ ht)⟩
      ⟨f, hf, Subtype.ext (by
        rw [Subalgebra.coe_pow, Subalgebra.coe_pow, ← pow_mul, mul_comm, pow_mul]
        exact congrArg (· ^ q) ht)⟩ hy'
    exact hy.symm.trans (congrArg Subtype.val this)
  have hTq : ∀ t ∈ Teich q Ω, ∀ n, t ^ n ∈ Teich q Ω := by
    rintro t ⟨f, hf, ht⟩ n
    exact ⟨f, hf, by rw [← pow_mul, mul_comm, pow_mul, ht]⟩
  have hφR : ∀ x ∈ R, φ x ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => rw [hφT x hx]; exact Algebra.subset_adjoin (hTq x hx q)
    | algebraMap v => rw [hφV]; exact Subalgebra.algebraMap_mem _ v
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hφn : ∀ t ∈ Teich q Ω, ∀ n, (φ ^ n) t = t ^ q ^ n := by
    intro t ht n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hφT _ (hTq t ht _), ← pow_mul, pow_succ]
  have hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Teich q Ω := by
    intro m ζ h
    obtain ⟨p, n, hp, hpm, hqp⟩ := exists_prime (V := V)
    have hne : p ≠ l := by
      rintro rfl
      exact hpm hlu
    have hco : Nat.Coprime q (l ^ m) := by
      rw [hq, hqp]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hl).2 hne)
    refine ⟨(l ^ m).totient, Nat.totient_pos.2 (pow_pos hl.pos m), ?_⟩
    have h1 := Nat.ModEq.pow_totient hco
    rw [pow_eq_pow_of_modEq h1 h, pow_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨F, _, _, hF, _, _, _, _⟩ := exists_fractionField (V := V) (Ω := Ω) K R
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : IsAlgClosure F Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  obtain ⟨hT1, hT2, σ, hσ⟩ := hT R F ⟨hSH.1, hSH.2.1, hSH.2.2.1, hF⟩ _ (irreducible_of_gen hg hπ) l hl
    (by simpa using hlu.map (algebraMap V R)) Ω
  have hRF : ∀ x : R, algebraMap F Ω (algebraMap R F x) = x := fun x =>
    (IsScalarTower.algebraMap_apply R F Ω x).symm
  have hσR : ∀ x ∈ R, σ x = x := fun x hx => by
    have := σ.commutes (algebraMap R F ⟨x, hx⟩)
    rwa [hRF] at this
  refine ⟨R, hRloc, σ.restrictScalars K, φ, hSH, hVR, fun c => ?_, fun s => ?_, hσR, fun x => ?_,
    fun m ζ h => ⟨hσR ζ (Algebra.subset_adjoin (hζ m ζ h)), hφT ζ (hζ m ζ h)⟩, ?_⟩
  · exact teich_quot_of_gen hg (maximalIdeal R) (maximalIdeal_of_gen hg).le c
  · obtain ⟨W, hW, h1, h2, h3, h4, -, f, hf, hWf⟩ := exists_stage hg s
    refine ⟨W, hW, h1, h2, h3, h4, f, hf, fun x hx => ?_⟩
    rw [hWf] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      have hx' : (x : Ω) ^ q ^ f = x := congrArg Subtype.val hx
      rw [hφn x ⟨f, hf, hx'⟩, hx']
    | algebraMap v =>
      show (φ ^ f) (algebraMap V Ω v) = algebraMap V Ω v
      rw [IsScalarTower.algebraMap_apply V K Ω, AlgEquiv.commutes]
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add (f := _), hx, hy]
    | mul x y _ _ hx hy => rw [Subalgebra.coe_mul, map_mul, hx, hy]
  · refine ⟨⟨φ x, hφR x x.2⟩, rfl, fun hu => ?_⟩
    obtain ⟨y, hy, hy'⟩ := hφ ⟨x, hle x.2⟩
    refine hy' ?_
    convert hu.map (Subalgebra.inclusion hle) using 1
    apply Subtype.ext
    simp [hy]
  · intro L h1 h2 h3 x hx
    obtain ⟨a1, a2, a3⟩ := hA K F Ω l L h1 h2 h3
    obtain ⟨m, ρ, hρ, hL⟩ := hT1 _ a1 a2 a3
    obtain ⟨ζ, hζp, hσρ⟩ := hσ m ρ hρ
    have hfrac : ∀ a : F, ∃ u v : R, v ≠ 0 ∧ algebraMap F Ω a = (u : Ω) / v := fun a => by
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      exact ⟨u, v, nonZeroDivisors.ne_zero hv, by rw [map_div₀, hRF, hRF]⟩
    obtain ⟨b1, b2⟩ := hB F Ω (l ^ m) q ρ ζ _ σ (φ : Ω →+* Ω) (pow_pos hl.pos m) hρ
      (by rw [hRF]; exact hφV π)
      (fun a => by
        obtain ⟨u, v, -, h⟩ := hfrac a
        refine ⟨algebraMap R F ⟨φ u, hφR u u.2⟩ / algebraMap R F ⟨φ v, hφR v v.2⟩, ?_⟩
        rw [h, map_div₀, map_div₀, hRF, hRF]; rfl)
      (hT2 m) hζp hσρ (hφT ζ (hζ m ζ hζp.pow_eq_one)) x
      (hL (IntermediateField.subset_adjoin F _ hx))
    refine ⟨b1.trans ?_, fun h => ?_⟩
    · have : ∀ (n : ℕ) (y : Ω), (σ ^ n) y = (σ.restrictScalars K ^ n) y := fun n => by
        induction n with
        | zero => intro y; rfl
        | succ n ih => intro y; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; rfl
      exact this _ _
    · obtain ⟨a, rfl⟩ := b2 h
      obtain ⟨u, v, hv, h⟩ := hfrac a
      have hv' : (v : Ω) ≠ 0 := fun e => hv (Subtype.ext e)
      exact ⟨u, u.2, v, v.2, hv', by rw [h, div_mul_cancel₀ _ hv']⟩

end GlobalTheory.SS.MaxUnr


open GlobalTheory.SS in
theorem GlobalTheory.SS.exists_maxUnramified_frobenius_tame : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :=
  GlobalTheory.SS.MaxUnr.main_of GlobalTheory.TameKummer.galois_of_prime_power_degree GlobalTheory.compositum_finite_normal_isPGroup
    GlobalTheory.kummer_twist_relation_and_fixed_field GlobalTheory.exists_arithFrobenius_absGalois
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTameStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  first | exact @GlobalTheory.SS.exists_maxUnramified_frobenius_tame | exact GlobalTheory.SS.exists_maxUnramified_frobenius_tame | (intros; apply GlobalTheory.SS.exists_maxUnramified_frobenius_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem iter_lift {R K Ω : Type} [CommRing R] [Field K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    (I : Ideal R) (φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ q ∈ I) (n : ℕ) (x : R) :
    ∃ y : R, algebraMap R Ω y = (φ ^ n) (algebraMap R Ω x) ∧ y - x ^ (q ^ n) ∈ I := by
  induction n with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hI⟩ := ih
    obtain ⟨z, hz, hJ⟩ := h y
    refine ⟨z, by rw [hz, hy, pow_succ', AlgEquiv.mul_apply], ?_⟩
    rw [← Ideal.Quotient.eq] at hI hJ ⊢
    rw [hJ, map_pow, hI, ← map_pow, ← pow_mul, pow_succ]

theorem pow_pow_fixed {k : Type} [Monoid k] (c : k) (a : ℕ) (h : c ^ a = c) (n : ℕ) : c ^ (a ^ n) = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_lift_frac {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (g : A →+* L) (hg : Function.Injective g) : ∃ j : K →+* L, j.comp (algebraMap A K) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a⟩

theorem isSemiAbelian_of_rational_torsion (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l)
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left)
    (W L R K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [Algebra K L] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K'] [Algebra R K'] [IsFractionRing R K']
    [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω] [IsLocalHom (algebraMap W R)]
    (hWR : Function.Injective (algebraMap W R)) (hRΩ : Function.Injective (algebraMap R Ω))
    (hcW : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hVΩ : (algebraMap W Ω).comp (algebraMap V W) = (algebraMap K Ω).comp (algebraMap V K))
    (hk : IsAlgClosed (IsLocalRing.ResidueField R)) (hlR : IsUnit (l : R))
    (p r₀ f : ℕ) (hp : p.Prime) (hpR : CharP (IsLocalRing.ResidueField R) p) (hr₀ : 1 ≤ r₀) (hf : 1 ≤ f)
    (hres : ∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r₀) ^ m) = c)
    (σ φ : Ω ≃ₐ[K] Ω) (hfix : ∀ w : W, (φ ^ f) (algebraMap W Ω w) = algebraMap W Ω w)
    (hφ : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ (p ^ r₀) ∈ IsLocalRing.maximalIdeal R)
    (hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ (p ^ r₀))
    (hL : ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L,
      φ (σ x) = (σ ^ (p ^ r₀)) (φ x) ∧ (σ x = x → ∃ a b : R, algebraMap R Ω b ≠ 0 ∧ x * algebraMap R Ω b = algebraMap R Ω a))
    (G : Over (Sp W)) [GrpObj G] (hG : SmConn G) (hmod : IsModel (L := L) P.A G)
    (hdim : SmoothOfRelativeDimension P.g G.hom)
    (N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left)
    (hN : AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N)
    (c : ℕ) (hc : 1 ≤ c)
    (hext : ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left,
      s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left) :
    IsSemiAbelian G := by
  classical
  obtain ⟨j', hj0⟩ := exists_lift_frac (K := K') (algebraMap R Ω) hRΩ
  have hj' : ∀ x : R, j' (algebraMap R K' x) = algebraMap R Ω x := fun x => RingHom.congr_fun hj0 x
  obtain ⟨i, hi⟩ := exists_lift_frac (K := L) ((algebraMap R K').comp (algebraMap W R))
    ((IsFractionRing.injective R K').comp hWR)
  replace hi := hi.symm
  have hjW : (j'.comp i).comp (algebraMap W L) = algebraMap W Ω := by
    rw [RingHom.comp_assoc, ← hi]
    exact RingHom.ext fun w => (hj' _).trans (IsScalarTower.algebraMap_apply W R Ω w).symm
  have hjK : (j'.comp i).comp (algebraMap K L) = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) ?_
    rw [RingHom.comp_assoc, ← hcW, ← RingHom.comp_assoc, hjW, hVΩ]
  obtain ⟨θ, hθ, hθK⟩ := GlobalTheory.T.grpScheme_points_model_over_field K W L P.A G hmod Ω (j'.comp i) hjK hjW
  obtain ⟨e, act, hact, he, hpair, hrel, hdef⟩ := GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints K P Ω l (p ^ r₀) hl htors σ φ K' j' hζ
    (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
      obtain ⟨a, b, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
      refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
      rw [map_div₀, hj', hj', div_eq_iff hb0]
      exact hab.symm⟩)
  have hcard := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1
  haveI := P.isAb.comm
  have hψ : (φ ^ f).toRingEquiv.toRingHom.comp (j'.comp i) = j'.comp i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors W) ?_
    rw [RingHom.comp_assoc, hjW]
    exact RingHom.ext fun w => hfix w
  obtain ⟨t, a, m, C, Q, H, U, hm, hH, hcnt, hQ, hU, hHU, hT⟩ :=
    GlobalTheory.T.frobenius_counts_integral_torsion_specialFibre W R Ω hRΩ hk p (r₀ * f) l hp hpR (Nat.mul_pos hr₀ hf) hl hlR
      (fun c => by
        obtain ⟨m, hm, h⟩ := hres c
        refine ⟨m, hm, ?_⟩
        rw [pow_mul, ← pow_mul _ f m, mul_comm f m, pow_mul _ m f]
        exact pow_pow_fixed c _ h f)
      (φ ^ f).toRingEquiv.toRingHom (fun w => hfix w)
      (fun x => by rw [pow_mul]; exact iter_lift _ φ _ hφ f x)
      G hG P.g hdim N hN (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) θ (act (φ ^ f))
      (fun x => hθ _ hψ _ _ (hact _ x))
  rw [← map_pow, ← pow_mul] at hU hHU
  have hqq : (p ^ (r₀ * f)) ^ m = (p ^ r₀) ^ (f * m) := by rw [pow_mul, ← pow_mul _ f m]
  rw [hqq] at hU hQ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hg : P.g ≤ t + a := by
    refine GlobalTheory.T.weight_le_add_of_torsion_pairing (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) Ω l ((p ^ r₀) ^ (f * m)) P.g t a c C hl h3
      (Nat.cast_ne_zero.2 hl.ne_zero) ?_ hc hcard e he (act σ) (act (φ ^ (f * m))) (hpair _) (hrel _)
      (fun x hx => Over.OverMorphism.ext ((hact σ x).trans (htors σ x hx))) H U Q ?_ hcnt hQ hU hHU
    · rw [← pow_mul]
      exact Nat.one_lt_pow (Nat.mul_pos hr₀ (Nat.mul_pos hf hm)).ne' hp.one_lt
    · intro n x hx hS
      obtain ⟨y, hy⟩ := hdef n x hx hS
      obtain ⟨y', hy'⟩ := hθK K' i j' rfl x y hy _ hi
      obtain ⟨s, hs₁, hs₂⟩ := hext y'
      refine (hH _).2 ⟨s, hs₁, ?_⟩
      rw [← hy', ← hs₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj0]
  have hproper : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    obtain ⟨ε, -⟩ := hmod
    haveI := P.isAb.proper
    rw [← Over.w ε.hom]
    have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj P.A).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    have : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
    infer_instance
  · clear hcard
    refine GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special W L G hG hproper _ _ ?_ ?_ (hT hg)
    · ext w
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
    · intro z
      obtain ⟨m, hm, h⟩ := hres z
      have h1 : 1 < (p ^ r₀) ^ m := by
        rw [← pow_mul]
        exact Nat.one_lt_pow (Nat.mul_pos hr₀ hm).ne' hp.one_lt
      refine ⟨Polynomial.X ^ ((p ^ r₀) ^ m) - Polynomial.X, ?_, by simp [h]⟩
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast h1

theorem potentialSemistable_rational_lTorsion_any_closure (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (IsLocalRing.ResidueField V)) (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l) (hlu : IsUnit (l : V))
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) :
    PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  classical
  obtain ⟨R, _, σ, φ, hSH, hloc, hres, hW, hσ, hφ, hζ, hL⟩ := GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt V K hfin l hl hlu Ω _ rfl
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V)
  obtain ⟨p, hpV⟩ := CharP.exists (IsLocalRing.ResidueField V)
  obtain ⟨r₀, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField V) p
  rw [← Nat.card_eq_fintype_card] at hq
  rw [hq] at hres hφ hζ hL
  have hpR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap V R)).injective p
  have hVΩ : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hRΩ : Function.Injective (algebraMap R Ω) := Subtype.val_injective
  have hVR : Function.Injective (algebraMap V R) := fun a b h => hVΩ (congrArg Subtype.val h)
  obtain ⟨K', _, _, hSH⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra R K'), SH R K' := ⟨_, _, _, hSH⟩
  haveI : IsFractionRing R K' := hSH.2.2.2
  obtain ⟨jK, hjK'⟩ := exists_lift_frac (K := K) ((algebraMap R K').comp (algebraMap V R))
    ((IsFractionRing.injective R K').comp hVR)
  letI : Algebra K K' := jK.toAlgebra
  have hcomp : (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) := hjK'.symm
  obtain ⟨s, c, hc, hgeo⟩ := GlobalTheory.T.exists_neronNeutralComponent_finite_level V K R K' hSH hcomp P
  obtain ⟨W, hWd, hs, hWc, hWf, hWl, f, hf, hfix⟩ := hW s
  obtain ⟨G, _, L, _, _, _, _, hG, hcW, hmod, hdim, ⟨N, hN⟩, hext⟩ := hgeo W hWd hs hWl
  have hlR : IsUnit (l : R) := by simpa using hlu.map (algebraMap V R)
  haveI : IsLocalHom (algebraMap W R) := hWl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_rational_torsion V K l hl h3 P Ω htors W L R K' Subtype.val_injective hRΩ hcW
      (IsScalarTower.algebraMap_eq V K Ω) hSH.2.2.1 hlR p r₀ f hp hpR r₀.2 hf hres σ φ (fun w => hfix w.1 w.2) hφ hζ
      (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
        obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hab⟩⟩)
      G hG hmod hdim N hN c hc hext
  have hVW : IsLocalHom (algebraMap V W) := ⟨fun v hv => by
    have : IsUnit (algebraMap V R v) := hv.map W.val
    exact (isUnit_map_iff (algebraMap V R) v).1 this⟩
  exact ⟨W, L, inferInstance, inferInstance, hWd, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcW, hWf, hVW, hWc, G, inferInstance, hmod, hsemi⟩

theorem potModel_of_rational_torsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl h3 hlu P htors
  exact potentialSemistable_rational_lTorsion_any_closure V K hfin l hl h3 hlu P (AlgebraicClosure K) htors

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemistable_of_rational_lTorsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_of_rational_torsion | exact GlobalTheory.SS.potModel_of_rational_torsion | (intros; apply GlobalTheory.SS.potModel_of_rational_torsion <;> assumption)
end
