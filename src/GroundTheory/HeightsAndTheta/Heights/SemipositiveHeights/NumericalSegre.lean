module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR


open GroundTheory.Heights₂.Heights.FieldNumbers in
theorem DivPushForwardLocalZero : FieldNumbers.DivPushForwardLocal.Statement.{0} := by
  have hq := DegZeroLocQuot.proof.{0}
  have hdzl := DegZeroLocLocal.proof hq
  have hdzn := DegZeroLocNoetherian.proof hq
  have hmh := MChartHomog.proof.{0}
  have hmd := MChartDehomog.proof.{0}
  have hmt := MChartTrdeg.proof hmh
  have hdzr := DegZeroLocalRing.proof hdzl hdzn
    (DegZeroLocDim.proof hmh hmt (MChartLocDim.proof hq hmd hmh))
  have hnum := ConeVarNumerator.proof hq
  have hcone := ConeLocalLength.proof LocalizedQuotientLength.proof
    (ConeLocalFlat.proof (ConePolyLocalization.proof hdzl (ConeVarUnit.proof hq hnum)
      ConeVarSurj.proof (ConeVarInj.proof hnum)))
  have hfr := DegZeroLocFrac.proof.{0}
  have hff := FibreFinite.proof.{0}
  have hint := SemilocalIntegral.proof ValuativeCentre.proof.{0}
  have hrank := SemilocalFiniteRank.proof hff
    (SemilocalFinite.proof hint
      (LocalIntegralClosureFinite.proof NoetherIntegralClosureFinite.proof
        (FunctionFieldFinite.proof hmd hmt) hq hmd hfr) hdzn) hfr
  have hfrd := FibreRelDim.proof.{0}
  have hlz := DegZeroLocLocalize.proof.{0}
  have hres := DegZeroLocResidue.proof.{0}
  have hmaxi := SemilocalMaxIdeals.proof hff hfrd (FibreNonempty.proof hrank hdzr)
    DegZeroLocUnits.proof DegZeroLocSeparate.proof hlz (SemilocalResidueLength.proof hres hrank hlz)
  have hlen := SemilocalLength.proof
    (SemilocalLengthSum.proof hff hrank hdzr FiniteAlgebraLengthSum.proof hmaxi) hfrd
    DivCycleMinimal.proof hcone
  exact DivPushForwardLocal.proof DivCycleMinimal.proof hcone hdzr hrank hlen

theorem FlagBundleDim.full : FlagBundleDim.Statement :=
  FlagBundleDim.proof TwistedDualGensSpan.proof
    (SpanBundleDim.proof PointIdealMultiProj.proof SpanBundleTrdegGe.proof SpanBundleTrdegLe.proof)

theorem NumericalSegre.full : NumericalSegre.Statement :=
  NumericalSegre.of_open FlagBundleDim.full FlagBundleSectionForms.proof
    (FlagBundleSectionDiv.proof FlagBundleDim.full MultAtOfSaturated.proof ProjIdealFormValue.proof
      TruncSpecialize.proof FlagBundleChartSection.proof)
    FlagLineSection.proof FlagLineDegree.proof DivPushForwardLocalZero

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem KleimanNefF.kleimanNef_field_of_alt (hT : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  have : V.IsPrime := hV.1.1
  have hVd := HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1
  set y := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V
  have hy : KH.mIdealOver F y = V :=
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    exact ⟨i, (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩
  have hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hy]
    exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2
  have hnef' : ∀ j, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (a j) := by
    intro j W hW hle hW1
    rw [hy] at hle
    have hWF : IsProjVarF W 1 :=
      ⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
        hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
    have h := hnef j W hWF hle
    rwa [HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF] at h
  have h := hT F K ι _ y n a hnz hrel hnef'
  rw [hy] at h
  rw [HilbertSamuel.KleimanNefF.eq_intNum hI n V a hV]
  exact h

theorem NefProductNonneg.unfolding_matrix_of_form (hS : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SegreRealise.Statement)
    (hA : GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd hnef
  obtain ⟨N, _, x, Ms, _, hsub, _, hiff, hnum⟩ := hS F K ι Ω y d μs hy hd
  rw [← hnum]
  exact hA F Ω N x d _ Ms hsub fun j => (hiff j).2 (hnef j)

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
