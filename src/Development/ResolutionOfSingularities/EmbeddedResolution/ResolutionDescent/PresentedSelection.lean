module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceFieldBaseChange
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem exists_baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    ∃ e : baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n,
      e.hom ≫ affineSpaceIndexedByToSpec K n = baseChangeToSpec (affineSpaceIndexedByToSpec k n) K := by
  have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
      (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
      (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
  have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
      (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
    AlgebraicGeometry.AffineSpace.isPullback_map (n := n) (specMapAlgebraMap k K)
  exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_snd _ _ hB⟩

def baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K] (n : Type u) :
    baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n :=
  (exists_baseChangeAffineSpaceIso k K n).choose

@[simp]
theorem baseChangeAffineSpaceIso_hom_comp_toSpec (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    (baseChangeAffineSpaceIso k K n).hom ≫ affineSpaceIndexedByToSpec K n =
      baseChangeToSpec (affineSpaceIndexedByToSpec k n) K :=
  (exists_baseChangeAffineSpaceIso k K n).choose_spec

def affineSpaceChartBaseChangeAmbientIso
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient ≅
      affineSpaceIndexedBy K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) :=
  baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))

def affineSpaceChartBaseChangePresentation
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ClosedEmbeddingIntoAffineSpace
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK) :=
  presentationOfAmbientIso hsm
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK)
    (hemb k Y pY).choose
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK)
    (by exact baseChangeAffineSpaceIso_hom_comp_toSpec k K (ULift.{u, 0} (Fin (hemb k Y pY).choose)))

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PresentedSelection where
  sel : EmbeddingChoice.{u}
  pres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], ClosedEmbeddingIntoAffineSpace (sel k Y p)
  basePres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents (Scheme.Hom.ker ((sel k Y p).baseChangeEmb K)))
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace ((sel k Y p).baseChange K hker hsnc)

theorem isCompatibleWithFieldBaseChange_toAffineResolutionRule (R : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u}) (hinv : R.IsIndependentOfPresentedEmbedding)
    (hfield : R.IsCompatibleWithFieldBaseChange)
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithFieldBaseChange (R.toAffineResolutionRule C.sel) := by
  intro k _ _ Y p _ _ _ _ K _ _ _ _ _
  have hlft : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have hqcb : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      ([] : List (baseChange (C.sel k Y p).ambientStruct K).IdealSheafData) :=
    hsnc K (baseChange (C.sel k Y p).ambientStruct K)
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec (C.sel k Y p) K)
  have hsq : IsPullback (baseChangeProjection p K) ((C.sel k Y p).baseChangeEmb K)
      (C.sel k Y p).emb (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    (EmbeddingDatum.isPullback_baseChangeEmb (C.sel k Y p) K).flip
  have hflat : AlgebraicGeometry.Flat (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    inferInstance
  have hqc1 : AlgebraicGeometry.QuasiCompact (C.sel k Y p).emb := inferInstance
  have hqc2 : AlgebraicGeometry.QuasiCompact ((C.sel k Y p).baseChangeEmb K) :=
    quasiCompact_of_isPullback hsq
  have hkerK : NonzeroOnComponents (Scheme.Hom.ker ((C.sel k Y p).baseChangeEmb K)) := by
    rw [ker_eq_comap_ker_of_isPullback_of_flat hsq]
    exact NonzeroOnComponents.comap_of_flat (C.sel k Y p).nonzeroOnComponents_ker _
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p (C.sel k Y p) K hkerK hsncK)
    (hinv K (baseChange p K) (baseChangeToSpec p K)
      ((C.sel k Y p).baseChange K hkerK hsncK)
      (C.sel K (baseChange p K) (baseChangeToSpec p K))
      (C.basePres k Y p K hkerK hsncK)
      (C.pres K (baseChange p K) (baseChangeToSpec p K)))

def affineSpacePresentedSelection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    PresentedSelection.{u} where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ _ _ =>
    let n := (hemb k Y p).choose
    presentationOfAmbientIso hsm _ n
      (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin n)))
      (baseChangeAffineSpaceIso_hom_comp_toSpec k K (ULift.{u, 0} (Fin n)))

@[simp]
theorem affineSpacePresentedSelection_selection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl

end FunctorialResolution.EmbeddedResolution

end
