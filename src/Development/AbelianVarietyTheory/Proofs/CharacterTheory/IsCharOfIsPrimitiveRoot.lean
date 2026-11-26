module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobius
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePowerStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_isPrimitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ G _ _ hG χ hχ
  refine GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character K L G χ hχ (GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower K L G (fun H hH ψ hψ => ?_) χ hχ)
  exact GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower K L m ζ hm hζ H (fun h => Subtype.ext (by simpa using hG (h : G))) hH ψ hψ
end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EssFiniteTypeOfFiniteDimensionalSubfieldClosure
namespace GlobalTheory

open Matrix Polynomial
open scoped BigOperators

theorem essFiniteType_of_finiteDimensional_subfield_closure {o Om : Type*} [CommRing o]
    [IsDomain o] [Field Om] [Algebra o Om] [FaithfulSMul o Om] {T : Set Om} (hT : T.Finite)
    (h : FiniteDimensional (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) Om) :
    Algebra.EssFiniteType o Om := by
  let K := FractionRing o
  letI : Algebra K Om := FractionRing.liftAlgebra o Om
  haveI : Algebra.EssFiniteType o K := .of_isLocalization K (nonZeroDivisors o)
  let E := IntermediateField.adjoin K T
  haveI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hT)
  have hle : Subfield.closure (Set.range (algebraMap o Om) ∪ T) ≤ E.toSubfield := by
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (IntermediateField.subset_adjoin K T))
    rintro _ ⟨x, rfl⟩
    rw [IsScalarTower.algebraMap_apply o K Om]
    exact E.algebraMap_mem _
  letI : Algebra (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om :=
    .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E Om :=
    .of_restrictScalars_finite (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om
  haveI : Algebra.EssFiniteType K Om := .comp K E Om
  exact .comp o K Om

end GlobalTheory
end
