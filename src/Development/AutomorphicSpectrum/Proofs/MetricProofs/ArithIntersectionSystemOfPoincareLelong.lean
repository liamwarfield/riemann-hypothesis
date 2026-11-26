module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartSheetCompare
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsMultiHomogIdealMapRedMap
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

abbrev redMap (ι : K → Type*) (p : ℕ) : MRing ι →+* MRingOver (ZMod p) ι :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap ι p) := by
  exact MvPolynomial.map_surjective _ ZMod.intCast_surjective

theorem natCast_charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs := rfl
  rw [hc]
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef
  have hg : C g ∈ W := Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)
  have h : C (g.natAbs : ℤ) ∈ W := by
    rcases Int.natAbs_eq g with h | h
    · rw [← h]; exact hg
    · have e : (g.natAbs : ℤ) = -g := by linarith
      rw [e, map_neg]; exact W.neg_mem hg
  rw [← map_natCast (C : ℤ →+* MRing ι) g.natAbs]
  exact h

theorem ker_redMap_le {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    RingHom.ker (redMap ι p) ≤ W := by
  rw [redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff]
  simpa using hp

theorem comap_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (W.map (redMap ι p)).comap (redMap ι p) = W := by
  rw [Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (ker_redMap_le hp)]

theorem isMultiHomog_redMap {p : ℕ} {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    IsMultiHomog (redMap ι p s) a := by
  intro m hm k
  refine h m ?_ k
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro h0
  apply hm
  simp [redMap, MvPolynomial.coeff_map, h0]

theorem isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, isMultiHomog_redMap ha⟩

theorem isRelevant_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx

def quotRedEquiv {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (MRing ι ⧸ W) ≃+* (MRingOver (ZMod p) ι ⧸ W.map (redMap ι p)) :=
  (Ideal.quotEquivOfEq (by
      rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_redMap hp])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (W.map (redMap ι p))).comp (redMap ι p))
      (Ideal.Quotient.mk_surjective.comp (redMap_surjective p)))

theorem isProjVarF_map_redMap {p : ℕ} [Fact p.Prime] {W : Ideal (MRing ι)} {n : ℕ}
    (hp : ((p : ℕ) : MRing ι) ∈ W) (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (redMap ι p)) n := by
  obtain ⟨hWp, hWh, hWr⟩ := hW
  refine ⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)
  · rw [← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]
    exact hdim

theorem fibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement := by
  intro K _ ι _ P n A s W hP hs hW hv
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have hmp : IsMultiProjPrime W := ⟨hWp, hWmh, hWrel⟩
  have hp := charOf_prime hWp hv
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  refine ⟨hp, natCast_charOf_mem W, hmp, ?_⟩
  haveI : Fact (charOf W).Prime := ⟨hp⟩
  exact isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim

end GlobalTheory.CompanionTheory.Ar.Pub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelong
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelong
namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights

theorem Seg.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Seg.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Seg.GoodChartDim

theorem Seg.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Seg.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Seg.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Seg.PtsGenericCount

theorem Seg.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Seg.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Seg.PtsSheetSimpleNull Seg.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Seg.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Seg.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Seg.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Seg.DiscriminantSheetCover

theorem Seg.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Seg.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Seg.AreaFormulaInjSet

theorem Seg.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Seg.AreaFormulaInj

theorem Seg.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Seg.ConeMapAreaOne

theorem Seg.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Seg.ConeSliceSheetParam Seg.ConeMapArea

theorem Seg.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Seg.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect.coneDimOfChowForm_full

theorem Seg.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Seg.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Seg.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Seg.PtsPosPartProjIndep Seg.PtsSegreChartFibreSum Seg.SegreChartAbsIntegrable

theorem Seg.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Seg.PtsSemiPosMassFinite

theorem Seg.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Seg.PtsPosDensIntegrable Seg.PtsPosPartProjIndep

theorem Seg.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Seg.SegreChartAbsIntegrable Seg.PtsSegreChartFibreSum

theorem Seg.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Seg.PtsIntegralProjIndep Seg.PtsIntegralSegreChartProj

theorem Seg.SegreChart : GroundTheory.Heights₂.Heights.SegreChart.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreChartDim Seg.SegreChartIntegral

theorem thmIExists (hPL : PoincareLelong) (hE : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  have hInt : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := ForSecondHalf.PtsIntegrable.of_resExists hE
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hInt (Inter.PtsAbsMeasurable.proof hE)
  have hBil : PtsBilinear.Statement := PtsBilinear.proof hAbs PtsSumMeasurable.proof
  have hSt : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found hBil HilbertSamuel.Closed.SegrePartition Seg.SegreChart
      AutoClose.StokesOnVariety
  have hLe : Inter.DeLeSemiPos.Statement :=
    Inter.DeLeSemiPos.proof hPL hSt (Inter.PtsAddFirst.proof hInt) (Inter.PtsRegLimit.proof hInt hAbs)
      (Inter.PtsMonoSemiPos.of_remaining hInt) Inter.RegCurvBound.full Inter.HorizNotMem.full
  have hPL2 : ReciprocityTheory.ChartRestriction.G.Geo.SectionSpaceSymmetry :=
    Inter.ProjectiveLineTwo.proof (Inter.DeSlotAdd.proof hE) Inter.SemiPosTwist.full hLe
  have hSwap : Inter.Swap.Statement := Inter.Swap.proof Inter.SwapCycles.full Inter.GeoNumCut.full hPL2
  have hRS : Inter.RPositionAdd.Statement := Inter.RPositionAdd.of_remaining hInt
  have hSymm : Inter.ThmISymm.Statement :=
    Inter.ThmISymm.proof hSwap hRS fibreComp
      (fun p _ K _ ι _ => Targets.ExistsUnique.full (ZMod p) ι)
      (fun p _ K _ ι _ => Targets.SymmStatement.of_type (ZMod p) ι)
      (fun K _ ι _ => GroundTheory.Heights₂.Heights.geoNumStatement ι)
  exact Inter.ThmIExists.proof AutoClose.Inter_R1Indep (Inter.RMul.proof hInt)
    (Inter.WellDefined.proof hSwap hRS) hSymm

end GlobalTheory.CompanionTheory.Ar.Pub
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelongStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_exists_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | exact GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.thmIExists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I4

theorem contractMixed_closed : ContractMixedStatement :=
  have hIntZero : Inter.PFIntZero.Statement :=
    Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)
  have hVert : Inter.PFVert.Statement :=
    Inter.PFVert.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _) Targets.contractMixedField
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    hIntZero hVert

theorem arithIntersectionSystem_of_poincareLelong_resK :
    GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := fun hPL hRK =>
  Targets.ArithIntersectionSystem.of_found
    (GlobalTheory.T.intersection_exists_of_poincare_lelong hPL (GlobalTheory.T.resolution_exists_of_resolution_statement hRK))
    (GlobalTheory.T.degree_and_coordinates_of_resolution (GlobalTheory.T.resolution_exists_of_resolution_statement hRK)).2
    contractMixed_closed

end GlobalTheory.CompanionTheory.Ar.Pub
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_system_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK | exact GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK <;> assumption)
end
