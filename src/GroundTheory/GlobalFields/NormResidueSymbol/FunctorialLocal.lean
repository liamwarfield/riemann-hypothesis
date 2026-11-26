module

public import GroundTheory.LocalFields.MainTheorem
public import GroundTheory.GlobalFields.NormResidueSymbol.RationalDiagonal
public import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

@[expose] public section

section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
section -- merged from GroundTheory.LocalFields.LocalArtinAbstractField
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section Embedding

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsSepClosure K Ω] in
theorem isAbelianGalois_fieldRange (ι : L →ₐ[K] Ω) : IsAbelianGalois K ι.fieldRange :=
  have := IsGalois.of_algEquiv ι.equivFieldRange
  { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective
      ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsAbelianGalois K L]
  [IsSepClosure K Ω] in
theorem finiteDimensional_fieldRange (ι : L →ₐ[K] Ω) : FiniteDimensional K ι.fieldRange :=
  LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv

def artinOfEmbedding (ι : L →ₐ[K] Ω) : Kˣ →* (L ≃ₐ[K] L) :=
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  (AlgEquiv.autCongr ι.equivFieldRange).symm.toMonoidHom.comp
    ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω))

theorem apply_artinOfEmbedding (ι : L →ₐ[K] Ω) (x : Kˣ) (z : L) :
    ι (artinOfEmbedding ι x z) =
      ((localArtinMap K Ω x ⟨ι z, (have := isAbelianGalois_fieldRange ι;
        le_maximalAbelianExtension ι.fieldRange) ⟨z, rfl⟩⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have h : ι (artinOfEmbedding ι x z) =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x)
        (ι.equivFieldRange z) : ι.fieldRange) : Ω) := by
    simp only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  rw [h, restrictAb_apply]
  rfl

theorem artinOfEmbedding_eq (ι₁ ι₂ : L →ₐ[K] Ω) : artinOfEmbedding ι₁ = artinOfEmbedding ι₂ := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable ι₁.fieldRange Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange
    (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)
  have hφι : ∀ z : L, φ (ι₁ z) = ι₂ z := by
    intro z
    have := congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
  have ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w :=
    fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w
  ext x z
  have key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z) := by
    rw [← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]
    change τ (ι₁ (artinOfEmbedding ι₁ x z)) = _
    rw [apply_artinOfEmbedding ι₁]
    set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁;
      le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩
    have htw : t w = ⟨ι₂ z, (have := isAbelianGalois_fieldRange ι₂;
        le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ :=
      Subtype.ext ((ht w).trans (hφι z))
    have hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w) := by
      rw [← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]
    rw [← ht, ← hc, htw]
  exact ι₂.injective key

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [IsSepClosure K Ω']

theorem artinOfEmbedding_algEquiv_comp (ε : Ω ≃ₐ[K] Ω') (ι : L →ₐ[K] Ω) :
    artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) = artinOfEmbedding ι := by
  ext x z
  have key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) =
      ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z) := by
    rw [apply_artinOfEmbedding]
    change _ = ε (ι (artinOfEmbedding ι x z))
    rw [apply_artinOfEmbedding, localArtinMap_algEquiv_apply]
    rfl
  exact ((ε : Ω →ₐ[K] Ω').comp ι).injective key

end Embedding

section Intrinsic


variable (K L) in
def localArtinMapOfField : Kˣ →* (L ≃ₐ[K] L) :=
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  artinOfEmbedding (IsSepClosed.lift : L →ₐ[K] SeparableClosure K)

theorem localArtinMapOfField_eq_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (ι : L →ₐ[K] Ω) : localArtinMapOfField K L = artinOfEmbedding ι := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  let ε : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  rw [localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]
  exact artinOfEmbedding_eq _ _

theorem surjective_localArtinMapOfField : Function.Surjective (localArtinMapOfField K L) := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  intro σ
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange
    (AlgEquiv.autCongr ι.equivFieldRange σ)
  refine ⟨x, ?_⟩
  change (AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ
  rw [hx, MulEquiv.symm_apply_apply]

end Intrinsic

end GroundTheory.LocalField
end
end

namespace GroundTheory.Global

open LocalField

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem isAbelianGalois_of_isGalois : IsAbelianGalois k M :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem apply_mem_maximalAbelianExtension {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (z : M) : ι z ∈ maximalAbelianExtension k Ω :=
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  have := isAbelianGalois_fieldRange ι
  le_maximalAbelianExtension ι.fieldRange ⟨z, rfl⟩

theorem normResidueSymbol_eq_localArtinMapOfField :
    have := isAbelianGalois_of_isGalois (k := k) (M := M)
    normResidueSymbol k M = localArtinMapOfField k M := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  ext x z
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := k) x
  apply (residueEmbedding k M).injective
  change residueEmbedding k M _ = residueEmbedding k M _
  rw [residueEmbedding_normResidueSymbol hτ,
    localArtinMapOfField_eq_artinOfEmbedding (residueEmbedding k M), apply_artinOfEmbedding,
    localArtinMap_apply, ← hτ, topologicalAbelianizationEquiv_mk_apply]

theorem normResidueSymbol_apply_eq_localArtinMap {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (x : kˣ) (z : M) :
    ι (normResidueSymbol k M x z) =
      ((localArtinMap k Ω x ⟨ι z, apply_mem_maximalAbelianExtension ι z⟩ :
        maximalAbelianExtension k Ω) : Ω) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  rw [normResidueSymbol_eq_localArtinMapOfField, localArtinMapOfField_eq_artinOfEmbedding ι,
    apply_artinOfEmbedding]

variable {k' : Type*} [Field k'] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [CharZero k'] [Algebra k k'] [ValuativeExtension k k']
  [FiniteDimensional k k']
  {M' : Type*} [Field M'] [Algebra k' M'] [Algebra k M'] [IsScalarTower k k' M']
  [FiniteDimensional k' M'] [IsGalois k' M'] [IsMulCommutative (M' ≃ₐ[k'] M')]

theorem normResidueSymbol_norm (j : M →ₐ[k] M') (x : k'ˣ) (z : M) :
    normResidueSymbol k' M' x (j z) = j (normResidueSymbol k M (normUnits k k' x) z) := by
  have : IsSepClosure k (AlgebraicClosure k') :=
    isSepClosure_of_isSeparable k k' (AlgebraicClosure k')
  set ι' : M' →ₐ[k'] AlgebraicClosure k' := IsAlgClosed.lift
  set ι : M →ₐ[k] AlgebraicClosure k' := (ι'.restrictScalars k).comp j
  apply ι'.injective
  have h1 := normResidueSymbol_apply_eq_localArtinMap ι' x (j z)
  have h2 := normResidueSymbol_apply_eq_localArtinMap ι (normUnits k k' x) z
  have h3 := localArtinMap_apply_of_algebra (Ω := AlgebraicClosure k') x
    (apply_mem_maximalAbelianExtension ι z)
  exact h1.trans (h3.trans h2.symm)

end Local

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.Rational
section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic
namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h

abbrev cycRestrict : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic

theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := maxCyclotomic)
    (E := AlgebraicClosure ℚ)

theorem coe_cycRestrict_apply (σ : Gal(AlgebraicClosure ℚ/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : AlgebraicClosure ℚ) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x

theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2

def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))

theorem cycCharacter_cycRestrict (σ : Gal(AlgebraicClosure ℚ/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm
      (cycRestrict σ) = (σ : Gal(AlgebraicClosure ℚ/ℚ) ⧸ cycRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

theorem cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  apply Subtype.ext
  rw [cycCharacter_cycRestrict, SubmonoidClass.coe_pow]
  rw [coe_cycRestrict_apply]
  exact character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])

def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp _root_.GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)

theorem toPadicInt_unitPart (x : IdeleClassGroup ℚ) (q : Nat.Primes) :
    toPadicInt q (unitPart x : ℤ̂) =
      ((_root_.GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv x).2 : Π p : Nat.Primes, ℤ_[p]) q := by
  change toPadics (padicEquiv.symm _) q = _
  rw [← padicEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹

theorem cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by
  simp [reciprocityMap]

end RationalSymbol

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

attribute [local instance] galCommGroup

section Unit

def unitAt (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℤ_[prime v]ˣ :=
  Units.map ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv :
    v.adicCompletionIntegers ℚ →* ℤ_[prime v]) ((RationalIdeles.positiveSubgroupEquiv y).2 v)

theorem padicRingEquiv_finiteProj (y : RationalIdeles.positiveSubgroup)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    padicRingEquiv v (finiteProj v (y : IdeleGroup ℚ) : v.adicCompletion ℚ) =
      ((unitAt y v : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ (0 : ℕ) := by
  rw [pow_zero, mul_one]
  rfl

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    ideleSymbol ℚ L y ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀} fun v hv ↦ by
      rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (unitAt y v) 0
        (padicRingEquiv_finiteProj y v)
        (Nat.Coprime.pow_left n (coprime_prime (by simpa using hv : v ≠ v₀).symm)) hζ,
        pow_zero, pow_one],
    Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,
    extensionEmbeddingOfIsReal_infiniteProj,
    if_neg (not_lt.2 (RationalIdeles.mem_positiveSubgroup.1 y.2).2.le)]
  exact localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (unitAt y v₀) 0
    (by rw [padicRingEquiv_finiteProj y v₀, pow_zero, zpow_zero]) hζ

end Unit

theorem toPadicInt_unitPart_mk (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPadicInt (prime v) (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℤ̂) =
      ((unitAt y v : ℤ_[prime v]ˣ) : ℤ_[prime v]) := by
  have h := toPadicInt_unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
    (Rat.HeightOneSpectrum.primesEquiv v)
  rw [RationalIdeles.ideleClassGroupEquiv_mk] at h
  refine h.trans ?_
  change RationalIdeles.integersRingEquiv (fun v ↦ (((RationalIdeles.positiveSubgroupEquiv y).2 v :
    (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ))
      (Rat.HeightOneSpectrum.primesEquiv v) = _
  exact Equiv.piCongrLeft_apply_apply (P := fun p : Nat.Primes ↦ ℤ_[p])
    (e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
    (fun v' ↦ (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v').toAlgEquiv.toRingEquiv
      (((RationalIdeles.positiveSubgroupEquiv y).2 v' : (v'.adicCompletionIntegers ℚ)ˣ) :
        v'.adicCompletionIntegers ℚ)) v

theorem reciprocityMap_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : maxCyclotomic} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    reciprocityMap (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  rw [cycCharacter_spec _ (primePowPNat (prime v₀) n) hζ, cycCharacter_reciprocityMap,
    ← toZModPow_toPadicInt]
  have h' : Units.map (toPadicInt (prime v₀)).toMonoidHom
      (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v₀ :=
    Units.ext (toPadicInt_unitPart_mk y v₀)
  have h'' : toPadicInt (prime v₀)
      (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) =
        (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀]) := by
    rw [← h', Units.coe_map_inv]
    rfl
  rw [h'']
  rfl

instance (m : ℕ) [NeZero m] :
    IsMulCommutative (rootsOfUnityField m ≃ₐ[ℚ] rootsOfUnityField m) :=
  IsCyclotomicExtension.isMulCommutative {m} ℚ _

theorem rootsOfUnityField_le_maxCyclotomic (m : ℕ) [NeZero m] :
    rootsOfUnityField m ≤ maxCyclotomic :=
  adjoin_le_iff.2 fun _ hx ↦ subset_adjoin ℚ _ ⟨m, Nat.pos_of_neZero m, hx⟩

theorem restrictNormal_eq_ideleSymbol (m : ℕ) [NeZero m] (x : IdeleGroup ℚ)
    (σ : Gal(AlgebraicClosure ℚ/ℚ))
    (hσ : cycRestrict σ = reciprocityMap (IdeleClassGroup.mk ℚ x)) :
    σ.restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) x := by
  obtain ⟨⟨a, y⟩, rfl⟩ := RationalIdeles.mulMap_bijective.2 x
  simp only [RationalIdeles.mulMap_apply] at hσ ⊢
  have e : IdeleClassGroup.mk ℚ (diagonal ℚ a * (y : IdeleGroup ℚ)) =
      IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ) := by
    rw [map_mul, IdeleClassGroup.mk_diagonal]
    exact one_mul (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
  rw [e] at hσ
  rw [map_mul, ideleSymbol_diagonal_eq_one _ {m} a, one_mul]
  set L := rootsOfUnityField m
  set σ₁ := ideleSymbol ℚ L (y : IdeleGroup ℚ)
  set σ₂ := σ.restrictNormal L

  have key : ∀ (p k : ℕ) (hp : p.Prime) (ζ : L), ζ ^ (p ^ k) = 1 → σ₂ ζ = σ₁ ζ := by
    intro p k hp ζ hζ
    have hp' : ζ ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 := by rw [prime_placeOf ⟨p, hp⟩]; exact hζ
    rw [ideleSymbol_apply_of_mem_positiveSubgroup L y _ hp']
    apply Subtype.ext
    have h1 : ((σ₂ ζ : L) : AlgebraicClosure ℚ) = σ ζ :=
      AlgEquiv.restrictNormal_commutes σ L ζ
    have hmem : (ζ : AlgebraicClosure ℚ) ∈ maxCyclotomic :=
      rootsOfUnityField_le_maxCyclotomic m ζ.2
    have hζ' : (⟨ζ, hmem⟩ : maxCyclotomic) ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hp')
    have h2 := reciprocityMap_apply_of_mem_positiveSubgroup y (placeOf ⟨p, hp⟩) hζ'
    rw [← hσ] at h2
    have h3 := congrArg Subtype.val h2
    rw [coe_cycRestrict_apply] at h3
    rw [h1, h3, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  refine IsCyclotomicExtension.algEquiv_eq_of_apply_eq {m} ℚ L fun n hn hn0 ↦ ?_
  obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hn hn0
  refine ⟨r, hr, ?_⟩
  have := apply_eq_of_pow_eq_one_of_forall_prime_pow (σ₁⁻¹ * σ₂) (fun p k hp ζ hζ ↦ by
    rw [AlgEquiv.mul_apply, key p k hp ζ hζ, ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]) hn0 hr.pow_eq_one
  rw [AlgEquiv.mul_apply] at this
  calc σ₂ r = σ₁ (σ₁⁻¹ (σ₂ r)) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    _ = σ₁ r := by rw [this]

theorem coe_ideleSymbol_apply (m : ℕ) [NeZero m] (x : IdeleGroup ℚ) (z : rootsOfUnityField m) :
    ((ideleSymbol ℚ (rootsOfUnityField m) x z : rootsOfUnityField m) : AlgebraicClosure ℚ) =
      ((reciprocityMap (IdeleClassGroup.mk ℚ x)
        ⟨z, rootsOfUnityField_le_maxCyclotomic m z.2⟩ : maxCyclotomic) : AlgebraicClosure ℚ) := by
  obtain ⟨σ, hσ⟩ := cycRestrict_surjective (reciprocityMap (IdeleClassGroup.mk ℚ x))
  rw [← restrictNormal_eq_ideleSymbol m x σ hσ, ← hσ, coe_cycRestrict_apply]
  exact AlgEquiv.restrictNormal_commutes σ (rootsOfUnityField m) z

end RationalSymbol

end

end GroundTheory.Global
end
