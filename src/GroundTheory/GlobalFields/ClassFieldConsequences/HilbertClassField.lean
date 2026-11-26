module

public import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup SemiLocal
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension)
open scoped nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

abbrev hilbertClassField : IntermediateField K Ω :=
  (Modulus.one : Modulus K).rayClassField Ω

instance finiteDimensional_hilbertClassField : FiniteDimensional K (hilbertClassField K Ω) :=
  inferInstanceAs (FiniteDimensional K ((Modulus.one : Modulus K).rayClassField Ω))

instance isAbelianGalois_hilbertClassField : IsAbelianGalois K (hilbertClassField K Ω) :=
  inferInstanceAs (IsAbelianGalois K ((Modulus.one : Modulus K).rayClassField Ω))

theorem range_ideleClassNorm_hilbertClassField :
    (ideleClassNorm K (hilbertClassField K Ω)).range =
      (standardOpenSubgroup K).map (IdeleClassGroup.mk K) := by
  rw [← Modulus.congruenceSubgroup_one]
  exact (Modulus.one : Modulus K).range_ideleClassNorm_rayClassField Ω

theorem isUnramifiedEverywhere_hilbertClassField :
    IsUnramifiedEverywhere K (hilbertClassField K Ω) := by
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [isUnramifiedIn_iff_ramificationIdx]
    intro w hw
    have := hw
    exact (Modulus.one : Modulus K).ramificationIdx_rayClassField_eq_one Ω
      (Modulus.not_dvd_one_ideal v) w
  · rw [← infiniteLocalSymbol_eq_one_iff]
    ext1 x
    have hx : IdeleClassGroup.mk K (infiniteEmbedding v x) ∈
        (ideleClassNorm K (hilbertClassField K Ω)).range := by
      rw [range_ideleClassNorm_hilbertClassField]
      exact ⟨_, infiniteEmbedding_mem_standardOpenSubgroup v x, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk,
      ideleSymbol_infiniteEmbedding] at hx
    rw [hx, MonoidHom.one_apply]

theorem le_hilbertClassField_iff (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    L ≤ hilbertClassField K Ω ↔ IsUnramifiedEverywhere K L := by
  constructor
  · intro hle
    exact (isUnramifiedEverywhere_hilbertClassField K Ω).of_le hle
  · intro h
    refine (range_ideleClassNorm_le_range_iff L (hilbertClassField K Ω)).1 ?_
    rw [range_ideleClassNorm_hilbertClassField]
    rintro _ ⟨x, hx, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk]
    refine ideleSymbol_eq_one_of_isUnramifiedEverywhere K L h fun v ↦ ?_
    have hx' : x ∈ (Modulus.one : Modulus K).congruenceSubgroup := by
      rw [Modulus.congruenceSubgroup_one]
      exact hx
    have hv := ((Modulus.one : Modulus K).mem_congruenceSubgroup.1 hx').1 v
    rw [(Modulus.exponent_eq_zero_iff _ v).2 (Modulus.not_dvd_one_ideal v)] at hv
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
      (mem_unitsLevel.1 hv).1

def hilbertClassFieldArtinEquiv :
    ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) :=
  Modulus.classGroupEquiv.symm.trans ((Modulus.one : Modulus K).rayClassArtinEquiv Ω)

theorem hilbertClassFieldArtinEquiv_mk0 (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 (hilbertClassField K Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    hilbertClassFieldArtinEquiv K Ω
        (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      arithFrobAt (𝓞 K) (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) w.asIdeal := by
  change (Modulus.one : Modulus K).rayClassArtinEquiv Ω (Modulus.classGroupEquiv.symm
    (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) = _
  rw [← Modulus.classGroupEquiv_primeClass v, MulEquiv.symm_apply_apply]
  exact (Modulus.one : Modulus K).rayClassArtinEquiv_primeClass Ω (Modulus.not_dvd_one_ideal v) w

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ClassFieldConsequences.Conductor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup SemiLocal WithZero Function
open scoped NumberField.LiesOver

noncomputable section

universe u

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

variable (𝔪 : Modulus K)

theorem finiteEmbedding_mem_congruenceSubgroup_iff (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    finiteEmbedding v u ∈ 𝔪.congruenceSubgroup ↔ u ∈ unitsLevel v (𝔪.exponent v) := by
  constructor
  · intro h
    have := (𝔪.mem_congruenceSubgroup.1 h).1 v
    rwa [finiteProj_finiteEmbedding] at this
  · intro hu
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun w ↦ ?_, fun w _ ↦ ?_⟩
    · by_cases hwv : w = v
      · subst hwv
        rwa [finiteProj_finiteEmbedding]
      · rw [finiteProj_finiteEmbedding_of_ne hwv]
        exact one_mem _
    · rw [infiniteProj_finiteEmbedding, Units.val_one, map_one]
      exact one_pos

theorem infiniteEmbedding_mem_congruenceSubgroup {w : InfinitePlace K}
    (hw : ∀ w' ∈ 𝔪.real, w'.1 ≠ w) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w' hw' ↦ ?_⟩
  · rw [finiteProj_infiniteEmbedding]
    exact one_mem _
  · rw [infiniteProj_infiniteEmbedding_of_ne (hw w' hw'), Units.val_one, map_one]
    exact one_pos

end Modulus

section Conductor

variable (K) (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

def Modulus.conductor : Modulus K where
  ideal := ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ localConductorExponent L v
  ideal_ne_bot := finprod_asIdeal_pow_ne_bot _
  real := {w | infiniteLocalSymbol L w.1 ≠ 1}

variable {K}

namespace Modulus

theorem exponent_conductor (v : HeightOneSpectrum (𝓞 K)) :
    (conductor K L).exponent v = localConductorExponent L v := by
  rw [exponent, if_pos (FiniteMultiplicity.of_prime_left v.prime
    (conductor K L).ideal_ne_bot)]
  exact multiplicity_finprod_asIdeal_pow_eq (finite_support_localConductorExponent L) v

theorem conductor_dvd_iff (𝔪 : Modulus K) :
    conductor K L ∣ 𝔪 ↔ (∀ v, localConductorExponent L v ≤ 𝔪.exponent v) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, w ∉ 𝔪.real → infiniteLocalSymbol L w.1 = 1 := by
  rw [dvd_iff, ideal_dvd_ideal_iff]
  simp only [exponent_conductor]
  refine and_congr Iff.rfl ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · by_contra hne
    exact hw (h hne)
  · by_contra hn
    exact hw (h w hn)

theorem congruenceSubgroup_le_ker_ideleSymbol_iff (𝔪 : Modulus K) :
    𝔪.congruenceSubgroup ≤ (ideleSymbol K L).ker ↔ conductor K L ∣ 𝔪 := by
  rw [conductor_dvd_iff]
  constructor
  · intro h
    refine ⟨fun v ↦ ?_, fun w hw ↦ ?_⟩
    · rw [← unitsLevel_le_ker_localSymbol_iff]
      intro u hu
      have := h ((𝔪.finiteEmbedding_mem_congruenceSubgroup_iff v u).2 hu)
      rwa [MonoidHom.mem_ker, ideleSymbol_finiteEmbedding] at this
    · ext a : 1
      have hne : ∀ w' ∈ 𝔪.real, w'.1 ≠ w.1 := fun w' hw' heq ↦ hw (Subtype.ext heq ▸ hw')
      have := h (𝔪.infiniteEmbedding_mem_congruenceSubgroup hne a)
      rw [MonoidHom.mem_ker, ideleSymbol_infiniteEmbedding] at this
      rw [this, MonoidHom.one_apply]
  · rintro ⟨hf, hi⟩ x hx
    obtain ⟨hxf, hxi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
    rw [MonoidHom.mem_ker, ideleSymbol_apply]
    have h1 : ∀ v, localSymbol L v (finiteProj v x) = 1 := fun v ↦
      (unitsLevel_le_ker_localSymbol_iff L v).2 (hf v) (hxf v)
    have h2 : ∀ w, infiniteLocalSymbol L w (infiniteProj w x) = 1 := by
      intro w
      by_cases hw : w.IsReal
      · by_cases hm : (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real
        · obtain ⟨w'⟩ := IdeleNorm.nonempty_infinitePlacesOver L w
          rw [infiniteLocalSymbol_apply L w hw w', if_neg (not_lt.2 (hxi _ hm).le)]
        · rw [hi _ hm, MonoidHom.one_apply]
      · rw [infiniteLocalSymbol_of_not_isReal L w hw, MonoidHom.one_apply]
    simp only [h1, h2, finprod_one, Finset.prod_const_one, mul_one]

theorem map_congruenceSubgroup_le_range_ideleClassNorm_iff (𝔪 : Modulus K) :
    𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ (ideleClassNorm K L).range ↔
      conductor K L ∣ 𝔪 := by
  rw [← congruenceSubgroup_le_ker_ideleSymbol_iff, ← ker_reciprocityMap,
    Subgroup.map_le_iff_le_comap]
  exact Iff.rfl

end Modulus

end Conductor

section RayClassField

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

namespace Modulus

end Modulus

end RayClassField

end

end GroundTheory.Global
end
