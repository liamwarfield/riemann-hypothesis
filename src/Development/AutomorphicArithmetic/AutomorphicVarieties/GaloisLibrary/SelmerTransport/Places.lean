module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.RestrictScalarsTwistInvOver

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.places :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
      (A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v) ∧ (A = ⊤ → Ine (F := k) A = ⊥ ∧ ¬ A.valuation (l : Ω) < 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v → (A.valuation (l : Ω) < 1 ↔ v ∈ Above (F := k) l)) ∧
      (¬ A.valuation (l : Ω) < 1 → Ine (F := k) A ≤ (cycZ k Ω l).ker) := by
  intro k Ω _ _ _ _ _ l _ A
  have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := by
    intro z hz
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
    exact A.valuation_le_one y
  have hOk : ∀ x : 𝓞 k, A.valuation (algebraMap k Ω (x : k)) ≤ 1 := fun x =>
    hint _ x.isIntegral_coe.algebraMap
  have hl1 : A.valuation (l : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A l)
  have htop : A = ⊤ → ∀ y : Ω, A.valuation y < 1 → y = 0 := by
    intro hA y hy
    by_contra h0
    have h2 : A.valuation y⁻¹ ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _)
    have h3 : A.valuation y * A.valuation y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    have h4 : A.valuation y * A.valuation y⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hy
    exact absurd h3 (ne_of_lt h4)
  have hlne : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hA
    let p : Ideal (𝓞 k) :=
      { carrier := {x | A.valuation (algebraMap k Ω (x : k)) < 1}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_add (f := _)] at *
          exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
        zero_mem' := by simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hOk c)) hx }
    have hprime : p.IsPrime := by
      refine ⟨?_, ?_⟩
      · rw [Ne, Ideal.eq_top_iff_one]
        show ¬ A.valuation (algebraMap k Ω ((1 : 𝓞 k) : k)) < 1
        simp
      · intro x y hxy
        change A.valuation (algebraMap k Ω ((x * y : 𝓞 k) : k)) < 1 at hxy
        change A.valuation (algebraMap k Ω (x : k)) < 1 ∨ A.valuation (algebraMap k Ω (y : k)) < 1
        simp only [map_mul] at hxy
        by_contra h
        push_neg at h
        have hx1 : A.valuation (algebraMap k Ω (x : k)) = 1 := le_antisymm (hOk x) h.1
        have hy1 : A.valuation (algebraMap k Ω (y : k)) = 1 := le_antisymm (hOk y) h.2
        rw [hx1, hy1, one_mul] at hxy
        exact lt_irrefl _ hxy
    have hne : p ≠ ⊥ := by
      intro hbot
      apply hA
      have hk : ∀ y : k, A.valuation (algebraMap k Ω y) ≤ 1 := by
        intro y
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 k) y
        have hb0 : (b : 𝓞 k) ≠ 0 := nonZeroDivisors.ne_zero hb
        have hbv : A.valuation (algebraMap k Ω (algebraMap (𝓞 k) k b)) = 1 := by
          refine le_antisymm (hOk b) (not_lt.mp fun h => hb0 ?_)
          have hbp : b ∈ p := h
          rw [hbot] at hbp
          exact (Submodule.mem_bot _).mp hbp
        rw [map_div₀, map_div₀, hbv, div_one]
        exact hOk a
      have hf : ∀ y : k, algebraMap k Ω y ∈ A := fun y => (A.valuation_le_one_iff _).mp (hk y)
      let f : k →+* A := (algebraMap k Ω).codRestrict A hf
      have hcomp : (algebraMap A Ω).comp f = algebraMap k Ω := by
        ext y
        rfl
      rw [eq_top_iff]
      intro z _
      have hz : IsIntegral A z := by
        obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := k) z
        refine ⟨q.map f, hqm.map f, ?_⟩
        rw [Polynomial.eval₂_map, hcomp]
        exact hq
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hz
      exact y.2
    exact ⟨⟨p, hprime, hne⟩, fun x => Iff.rfl⟩
  · intro hA
    refine ⟨?_, fun h => hlne (htop hA _ h)⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨-, hσ⟩ := hσ
    ext z
    have h1 := hσ z ((A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _))
    have h2 := htop hA _ h1
    rw [sub_eq_zero] at h2
    simpa using h2
  · intro v hv
    have h := hv (l : 𝓞 k)
    simp only [map_natCast] at h
    exact h
  · intro hl σ hσ
    obtain ⟨-, hσ⟩ := hσ
    have hl1' : A.valuation (l : Ω) = 1 := le_antisymm hl1 (not_lt.mp hl)
    have hfix : ∀ (n : ℕ) (t : Ω), t ^ (l ^ n) = 1 → σ t = t := by
      intro n t ht
      have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
      set N := l ^ n with hNdef
      have htI : IsIntegral ℤ t := IsIntegral.of_pow hN (by rw [ht]; exact isIntegral_one)
      have huN : (σ t) ^ N = 1 := by rw [← map_pow, ht, map_one]
      have huI : IsIntegral ℤ (σ t) := IsIntegral.of_pow hN (by rw [huN]; exact isIntegral_one)
      by_contra hne
      set u := σ t with hu
      set s := t ^ (N - 1) with hs
      have hst : s * t = 1 := by rw [hs, ← pow_succ, Nat.sub_add_cancel hN, ht]
      set w := u * s with hw
      have hwN : w ^ N = 1 := by
        rw [hw, mul_pow, huN, one_mul, hs, ← pow_mul, mul_comm (N - 1) N, pow_mul, ht, one_pow]
      have hw1 : w ≠ 1 := by
        intro h
        apply hne
        have h' : w * t = t := by rw [h, one_mul]
        rw [hw, mul_assoc, hst, mul_one] at h'
        exact h'
      have hsI : IsIntegral ℤ s := htI.pow _
      have hwI : IsIntegral ℤ w := huI.mul hsI
      have hval : A.valuation (w - 1) < 1 := by
        have hws : w - 1 = (u - t) * s := by rw [hw, sub_mul, mul_comm t s, hst]
        rw [hws, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint s hsI)) (hσ t (hint t htI))
      set c := ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, w ^ i with hc
      have hcI : IsIntegral ℤ c :=
        IsIntegral.sum _ fun j _ => IsIntegral.sum _ fun i _ => hwI.pow i
      have hid : (N : Ω) = (1 - w) * c := by
        rw [hc, Finset.mul_sum]
        simp_rw [mul_neg_geom_sum]
        rw [Finset.sum_sub_distrib, geom_sum_eq hw1, hwN, sub_self, zero_div, sub_zero]
        simp
      have hNv : A.valuation (N : Ω) = 1 := by
        rw [hNdef, Nat.cast_pow, map_pow, hl1', one_pow]
      have hlt : A.valuation (N : Ω) < 1 := by
        rw [hid, map_mul, Valuation.map_sub_swap]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint c hcI)) hval
      rw [hNv] at hlt
      exact lt_irrefl _ hlt
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    rw [MonoidHom.mem_ker]
    change cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G k Ω) Ω σ) = 1
    apply Units.ext
    rw [Units.val_one]
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_one]
    refine (modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ (l ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ht, Units.val_one]
    change σ (t : Ω) = _
    rw [hfix n _ ht']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp at ht'
      simp [ht']
    · haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
      rw [ZMod.val_one, pow_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)

theorem UpperTheory.V.Base.galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω
  intros
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _
    constructor
    · rintro h y ⟨x, rfl⟩
      simpa using h x
    · intro h x
      simpa using h _ ⟨x, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩,
        fun σ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩
  · intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  · rw [hset]
    exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

section Alg

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

private theorem algebraMap_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hne
  have hbot : (⊥ : Ideal O).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l])
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]
    exact hmax
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

private theorem length_quot [Module.Free ℤ_[l] O] : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  have hspan : Ideal.span {(l : O)} = (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, ← IsLocalRing.finrank_quotient_map (R := ℤ_[l]) (S := O)]
  letI : Field (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) := Ideal.Quotient.field _
  haveI : Module.Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l])
      (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

end Alg

theorem UpperTheory.V.Base.dvrFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧
      eO l O = Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) ∧ eO l O ≠ 0 ∧
      eO l O ≤ (Module.finrank ℤ_[l] O : ℕ∞) ∧ eO l O = IsDiscreteValuationRing.addVal O (l : O) ∧
      ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : O) := by
  intro l _ O _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := algebraMap_inj O
  haveI : CharZero O := charZero_of_injective_algebraMap hinj
  obtain ⟨hcomp, -, hlm, -, hfree, hloc⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfree
  haveI := hloc
  have hspan : Ideal.span {(l : O)} =
      (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by
      rw [map_natCast, h, map_zero]
    have h'' : ((l : ℕ) : ℤ_[l]) = 0 := hinj h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h'')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hval : IsDiscreteValuationRing.addVal O (l : O) = n :=
    IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  have he : eO l O = n := by
    show Module.length O (O ⧸ Ideal.span {(l : O)}) = n
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hlm (hu ▸ u.isUnit)
  refine ⟨hinj, hfree, hloc, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · show Module.length O (O ⧸ Ideal.span {(l : O)}) = _
    rw [hspan]
  · rw [he]
    exact_mod_cast hn0
  · rw [← length_quot (l := l) O]
    show Module.length O (O ⧸ Ideal.span {(l : O)}) ≤ _
    rw [IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)})]
    exact le_mul_of_one_le_right' (Order.one_le_iff_pos.2 Module.length_pos)
  · rw [he, hval]
  · intro m hm
    have hcop : IsCoprime (l : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hmu
    have hmm : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hmu
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have hab' : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → O) hab
      rw [← hab']
      exact add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hmm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

theorem UpperTheory.V.Base.normO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 →
      ‖(a : PadicAlgCl l)‖ ^ (eO l O).toNat = ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  intro l _ O _ _ a ha
  have hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)
  have hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg ((u : O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : ((l : O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : eO l O = IsDiscreteValuationRing.addVal O (l : O) := Ring.ord_eq_addVal (l : O)
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galEmbFam :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime],
      (∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A ∧ (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A) ∧
      Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l = shaFam E Ω l ∧ (cycZ k Ω l).comp (galEmb k E Ω) = cycZ E Ω l ∧
      ∀ e : ℤ, (LDataCardLeFinrank.qzG k Ω l e).comp (galEmb k E Ω) = LDataCardLeFinrank.qzG E Ω l e := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hD : ∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
    exact Iff.rfl
  have hI : ∀ A : ValuationSubring Ω, (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl
  refine ⟨fun A => ⟨hD A, hI A⟩, ?_, ?_, fun e => ?_⟩
  · ext D
    constructor
    · rintro ⟨D', ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩
      · exact Or.inl ⟨A, hl, hD A⟩
      · exact Or.inr ⟨A, hI A⟩
    · rintro (⟨A, hl, rfl⟩ | ⟨A, rfl⟩)
      · exact ⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩
      · exact ⟨_, Or.inr ⟨A, rfl⟩, hI A⟩
  · exact MonoidHom.ext fun _ => rfl
  · exact MonoidHom.ext fun _ => rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base
open TensorProduct nonZeroDivisors

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

private theorem qo_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  have hint : Algebra.IsIntegral ℤ_[l] O := Algebra.IsIntegral.of_finite ℤ_[l] O
  have hm : (⊥ : Ideal O) < IsLocalRing.maximalIdeal O :=
    bot_lt_iff_ne_bot.mpr (IsDiscreteValuationRing.not_a_field O)
  have hlt := Ideal.IsIntegral.comap_lt_comap (R := ℤ_[l]) hm
  have hP : ((⊥ : Ideal O).comap (algebraMap ℤ_[l] O)).IsPrime := Ideal.comap_isPrime _ _
  have hQ : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) ≠ ⊤ :=
    Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hbot : (⊥ : Ideal O).comap (algebraMap ℤ_[l] O) = ⊥ := by
    by_contra hne
    have hmax := hP.isMaximal hne
    exact hlt.ne (hmax.eq_of_le hQ hlt.le)
  rw [← RingHom.ker_eq_comap_bot] at hbot
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hbot

private theorem exists_padicInt_multiple_of_ne_zero (b : O) (hb : b ≠ 0) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ d : O, algebraMap ℤ_[l] O c = b * d := by
  have hint : Algebra.IsIntegral ℤ_[l] O := Algebra.IsIntegral.of_finite ℤ_[l] O
  have hne : Ideal.span {b} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have h := Ideal.IsIntegral.comap_ne_bot ℤ_[l] hne
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hc
  obtain ⟨d, hd⟩ := hc
  exact ⟨c, hc0, d, by rw [← hd, mul_comm]⟩

private theorem fractionRing_exists_padicInt_clear_denom (x : FractionRing O) :
    ∃ o : O, ∃ c : ℤ_[l], c ≠ 0 ∧
      x * algebraMap ℤ_[l] (FractionRing O) c = algebraMap O (FractionRing O) o := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨c, hc, d, hd⟩ := exists_padicInt_multiple_of_ne_zero l O b (nonZeroDivisors.ne_zero hb)
  refine ⟨a * d, c, hc, ?_⟩
  have hb' : algebraMap O (FractionRing O) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O), hd, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] in
private theorem tmul_qz_inv_mul_eq (o : O) (c d : ℤ_[l]) (hd : d ≠ 0) :
    (o ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] c)⁻¹ : QZ l)) =
      (o * algebraMap ℤ_[l] O d) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c * d))⁻¹ : QZ l) := by
  have hd' : algebraMap ℤ_[l] ℚ_[l] d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hd
  rw [mul_comm o, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
    Algebra.smul_def, map_mul]
  congr 2
  rw [mul_inv, mul_comm (algebraMap ℤ_[l] ℚ_[l] c)⁻¹, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

private theorem qo_equiv : Nonempty (QO l O ≃ₗ[O] KStar.Selmer.FracMod O (FractionRing O)) := by
  classical
  have hinjK : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O), RingHom.coe_comp]
    exact (IsFractionRing.injective O (FractionRing O)).comp (qo_inj l O)
  let ι : ℚ_[l] →+* FractionRing O := IsFractionRing.lift hinjK
  have hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] ℚ_[l] z) = algebraMap ℤ_[l] (FractionRing O) z :=
    fun z => IsFractionRing.lift_algebraMap hinjK z
  let g₁ : ℚ_[l] →ₗ[ℤ_[l]] FractionRing O :=
    { toFun := ι
      map_add' := map_add ι
      map_smul' := fun z q => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  let g₂ : ℚ_[l] →ₗ[ℤ_[l]] KStar.Selmer.FracMod O (FractionRing O) :=
    ((1 : Submodule O (FractionRing O)).mkQ.restrictScalars ℤ_[l]).comp g₁
  have hg₂ : ZlSub l ≤ LinearMap.ker g₂ := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (ι (algebraMap ℤ_[l] ℚ_[l] z)) :
      KStar.Selmer.FracMod O (FractionRing O)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hι, Submodule.mem_one]
    exact ⟨algebraMap ℤ_[l] O z, (IsScalarTower.algebraMap_apply ℤ_[l] O _ z).symm⟩
  let g₃ : QZ l →ₗ[ℤ_[l]] KStar.Selmer.FracMod O (FractionRing O) := (ZlSub l).liftQ g₂ hg₂
  let φ : QO l O →ₗ[O] KStar.Selmer.FracMod O (FractionRing O) := LinearMap.liftBaseChange O g₃
  have hφ : ∀ (a : O) (r : ℚ_[l]), φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)) =
      a • (Submodule.Quotient.mk (ι r) : KStar.Selmer.FracMod O (FractionRing O)) :=
    fun a r => LinearMap.liftBaseChange_tmul O g₃ a _
  have hrep := fractionRing_exists_padicInt_clear_denom l O
  choose o c hc hx using hrep
  let ψ₀ : FractionRing O → QO l O := fun x =>
    (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
  have spec : ∀ (x : FractionRing O) (p : O) (e : ℤ_[l]), e ≠ 0 →
      x * algebraMap ℤ_[l] (FractionRing O) e = algebraMap O (FractionRing O) p →
      ψ₀ x = (p ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] e)⁻¹ : QZ l)) := by
    intro x p e he hxe
    show (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) = _
    rw [tmul_qz_inv_mul_eq l O (o x) (c x) e he, tmul_qz_inv_mul_eq l O p e (c x) (hc x), mul_comm e (c x)]
    refine congrArg (· ⊗ₜ[ℤ_[l]] _) ?_
    apply IsFractionRing.injective O (FractionRing O)
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hxe]
    ring
  have ψ₀_add : ∀ x y, ψ₀ (x + y) = ψ₀ x + ψ₀ y := by
    intro x y
    rw [spec (x + y) (o x * algebraMap ℤ_[l] O (c y) + o y * algebraMap ℤ_[l] O (c x)) (c x * c y)
      (mul_ne_zero (hc x) (hc y)) ?_, TensorProduct.add_tmul]
    · show _ = (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) +
        (o y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c y))⁻¹ : QZ l))
      rw [tmul_qz_inv_mul_eq l O (o x) (c x) (c y) (hc y), tmul_qz_inv_mul_eq l O (o y) (c y) (c x) (hc x),
        mul_comm (c y) (c x)]
    · simp only [map_add (f := _), map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hx y]
      ring
  have ψ₀_smul : ∀ (a : O) x, ψ₀ (a • x) = a • ψ₀ x := by
    intro a x
    rw [spec (a • x) (a * o x) (c x) (hc x) ?_]
    · show _ = a • (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    · rw [Algebra.smul_def, mul_assoc, hx x, map_mul]
  have ψ₀_one : ∀ p : O, ψ₀ (algebraMap O (FractionRing O) p) = 0 := by
    intro p
    rw [spec _ p 1 one_ne_zero (by rw [map_one, mul_one]), map_one, inv_one]
    have h1 : (Submodule.Quotient.mk (1 : ℚ_[l]) : QZ l) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨1, by simp⟩
    rw [h1, TensorProduct.tmul_zero]
    rfl
  let ψL : FractionRing O →ₗ[O] QO l O :=
    { toFun := ψ₀
      map_add' := ψ₀_add
      map_smul' := ψ₀_smul }
  have hker : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker ψL := by
    intro x hx'
    obtain ⟨p, rfl⟩ := Submodule.mem_one.mp hx'
    exact ψ₀_one p
  let ψ : KStar.Selmer.FracMod O (FractionRing O) →ₗ[O] QO l O :=
    (1 : Submodule O (FractionRing O)).liftQ ψL hker
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    ext x
    show φ (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) =
      Submodule.Quotient.mk x
    have hne : algebraMap ℤ_[l] (FractionRing O) (c x) ≠ 0 := (map_ne_zero_iff _ hinjK).mpr (hc x)
    rw [hφ, map_inv₀, hι, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ← hx x, mul_inv_cancel_right₀ hne]
  · refine LinearMap.ext fun (t : O ⊗[ℤ_[l]] QZ l) => ?_
    induction t using TensorProduct.induction_on with
    | zero => exact ((ψ ∘ₗ φ).map_zero).trans (LinearMap.id (R := O) (M := QO l O)).map_zero.symm
    | tmul a q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
      show ψ (φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l))) =
        a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)
      rw [hφ, map_smul]
      show a • ψ₀ (ι r) = _
      obtain ⟨z, e, he, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) r
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      rw [spec _ (algebraMap ℤ_[l] O z) e he0 ?_]
      · rw [Algebra.algebraMap_eq_smul_one (A := O) z, TensorProduct.smul_tmul,
          ← Submodule.Quotient.mk_smul]
        show a • ((1 : O) ⊗ₜ[ℤ_[l]]
          (Submodule.Quotient.mk (z • (algebraMap ℤ_[l] ℚ_[l] e)⁻¹) : QZ l)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def, div_eq_mul_inv]
      · rw [map_div₀, hι, hι, div_mul_cancel₀ _ ((map_ne_zero_iff _ hinjK).mpr he0),
          IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O)]
    | add t₁ t₂ h₁ h₂ =>
      have hadd := (ψ ∘ₗ φ).map_add t₁ t₂
      rw [h₁, h₂] at hadd
      exact hadd

private theorem qo_len (a : O) :
    Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) = IsDiscreteValuationRing.addVal O a := by
  obtain ⟨e⟩ := qo_equiv l O
  rw [← KStar.TotallyRealRoots.length_torsionBy_fracMod (FractionRing O) a]
  apply LinearEquiv.length_eq
  refine e.ofSubmodules _ _ ?_
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_torsionBy_iff,
    LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← map_smul, hm, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [← map_smul, hy, map_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] in
private theorem qo_tor (m : QO l O) : ∃ n : ℕ, l ^ n • m = 0 := by
  refine TensorProduct.induction_on (motive := fun m : O ⊗[ℤ_[l]] QZ l => ∃ n : ℕ, l ^ n • m = 0)
    m ?_ ?_ ?_
  · exact ⟨0, smul_zero _⟩
  · intro o q
    have hq : ∃ n : ℕ, l ^ n • q = 0 := by
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖r‖ hl
      refine ⟨n, ?_⟩
      have hle : ‖((l ^ n : ℕ) : ℚ_[l]) * r‖ ≤ 1 := by
        rw [norm_mul, Nat.cast_pow, norm_pow, Padic.norm_p, inv_pow,
          inv_mul_le_iff₀ (by positivity), mul_one]
        exact hn.le
      have hmem : ((l ^ n : ℕ) : ℚ_[l]) * r ∈ ZlSub l :=
        LinearMap.mem_range.mpr ⟨⟨_, hle⟩, rfl⟩
      show (Submodule.Quotient.mk (l ^ n • r) : ℚ_[l] ⧸ ZlSub l) = 0
      rw [nsmul_eq_mul, Submodule.Quotient.mk_eq_zero]
      exact hmem
    obtain ⟨n, hn⟩ := hq
    refine ⟨n, ?_⟩
    have h := map_nsmul (TensorProduct.mk ℤ_[l] O (QZ l) o) (l ^ n) q
    rw [hn, map_zero] at h
    exact h.symm
  · rintro x y ⟨n, hn⟩ ⟨k, hk⟩
    refine ⟨n + k, ?_⟩
    have h1 : l ^ (n + k) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hn, smul_zero]
    have h2 : l ^ (n + k) • y = 0 := by rw [pow_add, mul_smul, hk, smul_zero]
    rw [smul_add, h1, h2, add_zero]

end

theorem UpperTheory.V.Base.qoFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      (∀ m : QO l O, Module.length O (Submodule.span O {m}) ≠ ⊤) ∧ (∀ m : QO l O, ∃ n : ℕ, l ^ n • m = 0) ∧
      (∀ a : O, a ≠ 0 → ∀ m : QO l O, ∃ m' : QO l O, a • m' = m) ∧
      ∀ a : O, Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) = IsDiscreteValuationRing.addVal O a := by
  intro l _ O _ _ _ _ _
  obtain ⟨e⟩ := qo_equiv l O
  refine ⟨fun m => ?_, qo_tor l O, fun a ha m => ?_, qo_len l O⟩
  · obtain ⟨n, hn⟩ := qo_tor l O m
    have hb : ((l ^ n : ℕ) : O) ≠ 0 := by
      rw [← map_natCast (algebraMap ℤ_[l] O), map_ne_zero_iff _ (qo_inj l O), Nat.cast_ne_zero]
      exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have hle : Submodule.span O {m} ≤
        LinearMap.ker (((l ^ n : ℕ) : O) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul O, hn]
    intro htop
    have hlen := Module.length_le_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
    rw [htop, qo_len l O, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at hlen
    exact hb hlen
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (e m)
    have ha' : algebraMap O (FractionRing O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr ha
    refine ⟨e.symm (Submodule.Quotient.mk (x / algebraMap O (FractionRing O) a)), ?_⟩
    have hdiv : a • (x / algebraMap O (FractionRing O) a) = x := by
      rw [Algebra.smul_def]
      field_simp
    rw [← map_smul, ← Submodule.Quotient.mk_smul, hdiv, hx, e.symm_apply_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galQuot :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E],
      Function.Surjective (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)) ∧
      (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)).ker = galOf k E Ω ∧
      ∀ σ : G k Ω, IsLift (AlgEquiv.restrictNormalHom E σ : E ≃ₐ[k] E).toRingEquiv σ.toRingEquiv := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Normal k Ω := IsAlgClosure.normal k Ω
  have hc : ∀ (σ : G k Ω) (x : E),
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) := by
    intro σ x
    exact (AlgEquiv.restrictNormal_commutes σ E x).symm
  refine ⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, ?_⟩
  · ext σ
    rw [MonoidHom.mem_ker]
    change _ ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x
    constructor
    · intro h x
      rw [hc, h]
      rfl
    · intro h
      ext x
      apply (algebraMap E Ω).injective
      rw [← hc, h]
      rfl
  · intro σ x
    exact hc σ x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))
  exact hz ▸ z.2

open Polynomial in
private theorem key {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : ℤ[X]) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A)
    (fa : aeval a f = 0) (fb : aeval b f = 0) (hab : A.valuation (b - a) < 1)
    (hd : ¬ A.valuation (aeval a (derivative f)) < 1) : b = a := by
  by_contra hne
  apply hd
  obtain ⟨c, hc⟩ := (f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)
  have e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g := fun g x => by
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm
  rw [add_sub_cancel, derivative_map] at hc
  have h2 := congrArg (fun x : A => (x : Ω)) hc
  push_cast at h2
  simp only [e, fa, fb] at h2
  have h3 : aeval a (derivative f) = -(c : Ω) * (b - a) := by
    apply mul_right_cancel₀ (sub_ne_zero.2 hne)
    linear_combination -h2
  rw [h3, map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab

open Polynomial in
private theorem fix_int {k E' Ω : Type} [Field k] [NumberField k] [Field E'] [NumberField E'] [Field Ω] [Algebra k Ω]
    [Algebra E' Ω] (α : 𝓞 E') : ∃ d : ℤ, d ≠ 0 ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (d : Ω) < 1 →
      ∀ σ ∈ Ine (F := k) A, σ (algebraMap E' Ω α) = algebraMap E' Ω α := by
  have hi : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hne : aeval α (derivative (minpoly ℤ α)) ≠ 0 := by
    intro h
    have h1 := minpoly.isIntegrallyClosed_dvd hi h
    have h2 := minpoly.natDegree_pos hi
    have h3 : derivative (minpoly ℤ α) ≠ 0 := fun h0 => by
      have := natDegree_eq_zero_of_derivative_eq_zero h0
      omega
    have h4 := natDegree_le_of_dvd h1 h3
    have h5 := natDegree_derivative_lt (p := minpoly ℤ α) (by omega)
    omega
  set δ := aeval α (derivative (minpoly ℤ α)) with hδ
  have hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ} := by
    have := Ideal.absNorm_mem (Ideal.span {δ})
    rw [Ideal.absNorm_span_singleton] at this
    rcases Int.natAbs_eq (Algebra.norm ℤ δ) with h | h
    · rw [h]; simpa using this
    · rw [h]; simpa using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩
  let φ : 𝓞 E' →ₐ[ℤ] Ω := ((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom
  have hφ : ∀ x, φ x ∈ A := fun x => mem_of_int A ((Algebra.IsIntegral.isIntegral x).map φ)
  let ψ : Ω →ₐ[ℤ] Ω := σ.toRingEquiv.toRingHom.toIntAlgHom
  have fa : aeval (φ α) (minpoly ℤ α) = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  change ψ (φ α) = φ α
  refine key A (minpoly ℤ α) (hφ α) (mem_of_int A ((hi.map φ).map ψ)) fa
    (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_
  rw [aeval_algHom_apply, ← hδ] at h
  have e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ := by rw [← map_mul, ht, map_intCast]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h

open Polynomial in
private theorem fix_root {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {N : ℕ} (hN : N ≠ 0)
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (N : Ω) < 1) {σ : G k Ω} (hσ : σ ∈ Ine (F := k) A) {z : Ω}
    (hz : z ^ N = 1) : σ z = z := by
  have hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A := fun {y} hy =>
    mem_of_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))
  have hz' : (σ z) ^ N = 1 := by rw [← map_pow, hz, map_one]
  refine key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz'])
    (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_
  have e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X])) := by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast, map_pow, aeval_X]
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h

theorem UpperTheory.V.Base.ramFinite :
    ∀ (k E E' Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
      [Algebra k Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [Algebra k E] [IsScalarTower k E Ω] [IsScalarTower E E' Ω]
      [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω],
      (∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω) ∧
      ∀ (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} E E'] (A : ValuationSubring Ω), ¬ A.valuation (N : Ω) < 1 →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω := by
  intro k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  refine ⟨?_, fun N _ hc A hA σ hσ x => ?_⟩
  · choose d hd0 hd using fun α : 𝓞 E' => fix_int (k := k) (Ω := Ω) α
    have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) |
        v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite := fun i =>
      Ideal.finite_factors (by simpa using hd0 _)
    refine ⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Ideal.dvd_span_singleton] at hv
    have h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap =
        (algebraMap E' Ω).toRatAlgHom.toLinearMap := (integralBasis E').ext fun i => by
      rw [integralBasis_apply]
      refine hd _ A (fun h => hv i ((hA _).1 ?_)) σ hσ.2
      simpa using h
    exact LinearMap.congr_fun h x
  · have hx := hc.adjoin_roots x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, h0, hy⟩ := hy
      obtain rfl : n = N := hn
      exact fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])
    | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact hσ.1 r
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end
