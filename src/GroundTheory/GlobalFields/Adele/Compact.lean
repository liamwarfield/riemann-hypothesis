module

public import GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.IdeleGroups.Restricted

@[expose] public section

section -- merged from GroundTheory.GlobalFields.Adele.Compact
namespace GroundTheory.Global

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.Adele.Topology
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

variable (K : Type*) [Field K] [NumberField K]

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩

instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

theorem t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstance

instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem t2Space_adeleRing : T2Space 𝔸[K] :=
  inferInstance

instance IdeleGroup.locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

instance locallyCompactSpace_units_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  inferInstance

instance locallyCompactSpace_units_infiniteAdeleRing :
    LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  inferInstance

end GroundTheory.Global
end
