module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def NilIsStrictNormalCrossingsOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
    (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []

theorem nilIsStrictNormalCrossingsOfSmooth : NilIsStrictNormalCrossingsOfSmooth.{u} := by
  intro k _ _ A q hq
  have : AlgebraicGeometry.Smooth q := hq
  exact inStrictNormalCrossingPosition_nil q

theorem hasProperCenters_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) :
    (embeddedResolutionRuleOfPrincipalization A h).HasProperCenters := by
  intro k _ _ Y p _ _ _ _ D i hi
  have hi' : i < ((D.toEmbeddedBlowupSequence A).inducedBlowups (h k Y p D)).withoutIsoBlowups.length := hi
  exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top _ hi'

theorem toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by
  funext k _ _ Y p _ _ _ _
  rw [EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]
  exact embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum A h hemb hsnc hsm hw k Y p

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldBaseChangeAdmissible
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) : (T.baseChange L f).IsAdmissible := by
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base L f) :=
    instFlatSpecMapOfFieldHom T.base L f
  have hfst : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  · exact
      (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact hV.nonzeroOnComponents.comap_of_flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  · exact
      (inferInstance : AlgebraicGeometry.QuasiCompact
        (pullback.snd T.structMap (specMapOfFieldHom T.base L f)))
  · exact smooth_pullbackSnd_specMap T.structMap (CommRingCat.ofHom f)
  · exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (CommRingCat.ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
end
end
