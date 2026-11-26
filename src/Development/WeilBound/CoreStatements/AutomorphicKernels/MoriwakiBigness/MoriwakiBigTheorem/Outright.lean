module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.KeyFormulaVanishingCechMultInvariants
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGen
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechComplex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechExact
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerHeightsirational
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockVeronese
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSeparatedSmallCount
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAmpleCountAlongMultiplesX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNumberFieldBoxCountX
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftCountAlongMultiples
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyConditional
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfAis
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IntersectionNumberEqLineHeight
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelBlock.HSMBlock
namespace PositivityTheory.LocalParametersCuspidal.MB.HSM

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
  ReciprocityTheory.ChartRestriction.G.AI.I1

theorem theoremHSMBlock (hAIS : ArithIntersectionSystemStatement) (hResK : ResK.ResKStatement) :
    TheoremHSMBlock.Statement := by
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hResK
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hPF : PFCoordStatement := (GlobalTheory.T.degree_and_coordinates_of_resolution hRes).2
  have hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι := Targets.existsUniqueAll
  have hGF : GenFibreExistsStatement := Targets.genFibreExists
  have hIso : IsomInvariance.Statement := IsomInvariance.proof (Inter.RatR.proof hPts)
  have hCM : ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr hIso GraphIsometric.proof
  have hDim : FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hDG : Inter.DegreeGeneric.Statement :=
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hPts (Inter.PtsAbsMeasurable.proof hRes)
  have h6 : ProjFrameGraphDeg.Statement :=
    ProjFrameGraphDeg.proof hEU ProjFrameFibrePt.full ProjFrameFibreDeg.full
  have h15 : GraphChangeOfModel.Statement :=
    GraphChangeOfModel.proof hAI3 hGr hGF hEU hIso GraphIsometricForms.full
  have h16 : BlockGraphDeg.Statement :=
    BlockGraphDeg.proof hGr BlockGraphImage.full hGF hDim hEU Closed.Inter.ChartRankAdjoin
      BlockGraphFibreRatio.full
  have h18 : VeroneseGraphDeg.Statement :=
    VeroneseGraphDeg.proof hGr VeroneseGraphImage.full hDim hEU
  exact TheoremHSMBlock.of_open TwoBlockPieceIndex.proof TwoBlockModuleFinite.proof
    ModulePieceHilbert.proof TwoBlockModuleCycle.proof hPF hCM h6
    (HSMTransport.proof KrullDimMatAct.proof)
    (ResolutionDegree.proof PullFSExtension.full ProjFSMass.proof) ResolutionMixedBridge.full
    (BlockResolutionImageSup.proof ChartSupBound.full)
    (BlockResolutionDegreeIntegral.proof (GenDegGeomDeg.proof hDG)) BlockResolutionMixedBridge.full
    hAbs BlockImageInverse.proof h15 h16 VeroneseGramMono.proof h18

end PositivityTheory.LocalParametersCuspidal.MB.HSM
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.SegreJoinGeneration.GeneratesOverSegreJoinTwist
namespace PositivityTheory.KAmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsNef IsGenerated KAt baseDeg)
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization (segreJoin)

theorem kAt_all (d : ℕ) : KAt d := (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 d

theorem genTwistVanish : HilbertSamuel.GenTwistVanish.Statement :=
  HilbertSamuel.GenTwistVanish.proof PositivityTheory.HtPt.Ktw.a11 HilbertSamuel.QuotPartGraded.full
    (HilbertSamuel.GenKoszulStep.proof HilbertSamuel.KoszulCechComplex.proof HilbertSamuel.KoszulCechExact.proof
      HilbertSamuel.DoubleComplexVanish.full Kleiman.KHCechDSq.full Kleiman.KHCechDDeg.full)

theorem ampleOfGenTwist : HilbertSamuel.AmpleOfGenTwist.Statement :=
  HilbertSamuel.AmpleOfGenTwist.proof HilbertSamuel.GenTwistGenerated.full genTwistVanish

theorem generatesOver_segreJoin_twist {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ) {n : ℕ}
    (η : Fin n → Ω)
    (h : KH.GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ())) η) :
    KH.GeneratesOver S y (β + fun _ => c) η := by
  intro c0 hc
  obtain ⟨u, hu, hsum⟩ := h (Kleiman.SectionsOverLocalization.segreChart c0 c0)
    (Kleiman.SectionsOverLocalization.segreChart_adm y (Kleiman.SectionsOverLocalization.segreVec_ne_zero y hc) hc)
  refine ⟨u, fun j => Kleiman.SectionsOverLocalization.segre_diag_le y c0 (hu j), ?_⟩
  have e1 : ∀ k : K, segreJoin y ⟨Sum.inr k, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inr k)⟩ = y ⟨k, c0 k⟩ :=
    fun _ => rfl
  have e2 : segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ = ∏ k, y ⟨k, c0 k⟩ := rfl
  set D : Unit ⊕ K → ℤ := IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) with hD
  have e3 : ∀ k : K, D (Sum.inr k) = β k := by
    intro k
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have e4 : D (Sum.inl ()) = c := by
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have hprod : (∏ k, segreJoin y ⟨k, Kleiman.SectionsOverLocalization.segreChart c0 c0 k⟩ ^ (-D k)) =
      ∏ k, y ⟨k, c0 k⟩ ^ (-(β k + c)) := by
    rw [Fintype.prod_sum_type]
    have hu1 : (∏ u : Unit, segreJoin y ⟨Sum.inl u, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl u)⟩ ^
        (-D (Sum.inl u))) = (∏ k, y ⟨k, c0 k⟩) ^ (-c) := by
      rw [Fintype.prod_unique]
      show segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ ^ (-D (Sum.inl ())) = _
      rw [e2, e4]
    rw [hu1, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [e1, e3, ← zpow_add₀ (hc k)]
    congr 1
    ring
  rw [hprod] at hsum
  exact hsum

theorem generated_of_nef (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (α : K → ℤ)
    (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))
    (hnef : IsNef F y α) (t : ℚ) (ht : 0 < t) :
    ∃ (a' : ℕ) (m : ℤ), 1 ≤ a' ∧ (m : ℚ) = a' * t ∧ IsGenerated F y (a' • α + fun _ => m) := by
  obtain ⟨a', m, ha', hm, hva⟩ := kAt_all d F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ())
    (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
    ((Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hrel) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg α)
    ((Kleiman.SectionsOverLocalization.SegreNef.proof Kleiman.SectionsOverLocalization.SegreDim.proof Kleiman.SectionsOverLocalization.SegreNum.proof
      F K ι Ω y hnz α).2 hnef) t ht
  obtain ⟨n, x', hx', hgen, -⟩ := hva
  have e : a' • IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ()) =
      IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (a' • α) + m • baseDeg (Sum.inl ()) := by
    congr 1
    funext k
    cases k <;> simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Pi.mul_apply, Pi.natCast_apply]
  rw [e] at hx' hgen
  refine ⟨a', m, ha', hm, n, x', fun j => ?_, generatesOver_segreJoin_twist y (a' • α) m x' hgen⟩
  have := hx' j
  rwa [Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz] at this

theorem kAmp : KH.KAmpStatement := by
  intro F _ K _ _ ι _ _ I V d α b a hI hV hnef hb ha
  classical
  have : V.IsPrime := hV.1.1
  have hVd := HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1
  set y := Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V
  have hy : KH.mIdealOver F y = V :=
    Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    exact ⟨i, (Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩
  have hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hy]
    exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff V d).2 hV.2
  have hnef' : IsNef F y α := by
    intro W hW hle hW1
    rw [hy] at hle
    have hWF : IsProjVarF W 1 :=
      ⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
        hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
    have h := hnef W hWF hle
    rwa [HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF] at h
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have ha₀ : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨a', m, ha', hm, hgen⟩ :=
    generated_of_nef F K ι _ y d α hnz hrel hnef' ((a : ℚ) / (2 * b)) (by positivity)
  have hGV : KH.GeneratedV F V (a' • α + fun _ => m) := by
    have := Kleiman.SectionsOverLocalization.GeneratedCechTie.proof F K ι _ y _ hnz hgen
    rwa [hy] at this
  have hamp := ampleOfGenTwist F K ι V _ (a' * a) (2 * b) hV.1.2.1 hGV
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  have hm' : (2 * (b : ℤ)) * m = a' * a := by
    have hq : (2 * (b : ℚ)) * m = a' * a := by
      rw [hm]
      field_simp
    exact_mod_cast hq
  have e : ((2 * b : ℕ) : ℤ) • (a' • α + fun _ => m) + (fun _ => ((a' * a : ℕ) : ℤ)) =
      (2 * a') • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    push_cast
    linear_combination hm'
  rw [e] at hamp
  exact HilbertSamuel.ampleV_of_nsmul (by omega) hamp

end PositivityTheory.KAmp
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiSymmetry.EqMapSymm
set_option maxSynthPendingDepth 1

noncomputable section

namespace PositivityTheory.MbAis.DenseCurves

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CoverDenseAlt.Rename₂ CoverDenseAlt.HtF
open GroundTheory.Heights₂.Heights (blockIdx Cone BlockNonzero orbitIdeal ArithVariety chartMonomial)

theorem eq_map_symm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : K → ℕ}
    (e : ∀ k, ι k ≃ blockIdx n k) {W : Ideal (MRing ι)} {Q : Ideal (MRing (blockIdx n))}
    (h : W.map (ren e) = Q) : W = Q.map (ren fun k ↦ (e k).symm) := by
  ext f
  rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, h,
    ← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) Q (ren e f)]
  have : ren (fun k ↦ (e k).symm) (ren e f) = f := (ren e).symm_apply_apply f
  rw [this]

theorem main : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement := by
  intro K _ ι _ I P D H hI hP hH hHa
  classical
  haveI : Nonempty K := hP.1
  let n : K → ℕ := fun k ↦ Fintype.card (ι k) - 1
  have hn : ∀ k, Fintype.card (ι k) = n k + 1 := fun k ↦ by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    have : 0 < Fintype.card (ι k) := Fintype.card_pos_iff.2 ⟨i⟩
    simp only [n]
    omega
  let e : ∀ k, ι k ≃ blockIdx n k := fun k ↦ Fintype.equivFinOfCardEq (hn k)
  let Pv : ArithVariety n := CoverDenseAlt.Dense0.var e hP
  have hPv : Pv.ideal = P.map (ren e) := rfl
  obtain ⟨S, C₀, hS, hdense, hC₀⟩ := GroundTheory.Heights₂.Heights.DenseBoundedHeight.main K n Pv
  let B' : GroundTheory.Heights₂.Heights.HermLine n := toNum e H hH
  obtain ⟨m, C₁, hC₁⟩ := GroundTheory.Heights₂.Heights.HeightComparison.main K n Pv B'
  refine ⟨m * C₀ + C₁, {W | ∃ x ∈ S, W.map (ren e) = orbitIdeal x}, ?_, ?_⟩
  · rintro f ⟨a, ha⟩ hfP
    have hdens := (GroundTheory.Heights₂.Heights.zariskiDense_iff_orbitIdeal Pv S).mp hdense
    obtain ⟨W', ⟨x, hx, rfl⟩, hW'⟩ := hdens (ren e f) ⟨a, homog_ren e ha⟩
      (fun h ↦ hfP ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mp h))
    refine ⟨(orbitIdeal x).map (ren fun k ↦ (e k).symm), ⟨x, hx, ?_⟩, fun h ↦ hW' ?_⟩
    · ext g
      have h1 : g = ren e (ren (fun k ↦ (e k).symm) g) := ((ren e).apply_symm_apply g).symm
      rw [h1, GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e),
        GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm), ← h1]
    · have h1 : f = ren (fun k ↦ (e k).symm) (ren e f) := ((ren e).symm_apply_apply f).symm
      rw [h1] at h
      exact (GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren fun k ↦ (e k).symm) _ _).mp h
  · rintro W ⟨x, hxS, hWx⟩
    have hxP := hS hxS
    have hx : BlockNonzero x := hxP.1
    have hW : IsArithVar W 1 := by
      rw [eq_map_symm e hWx]
      exact arithVar_map _ (GroundTheory.Heights₂.Heights.OrbitCurve.full K n x hx)
    have hPW : P ≤ W := fun f hf ↦ by
      rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) W f, hWx]
      exact ((GroundTheory.Heights₂.Heights.mem_points_iff_le_orbitIdeal Pv x).mp hxP).2
        ((GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e) P f).mpr hf)
    refine ⟨hW, hPW, ?_⟩
    have hdeg' : degC (ι := blockIdx n) (orbitIdeal x) = degC W := by rw [← hWx, degC_map]
    have hdegN : 0 < degC W := hdeg' ▸ GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx
    have hdeg : (0 : ℝ) < degC W := by exact_mod_cast hdegN
    have hfin : Finite (GroundTheory.Heights₂.Heights.projPts W) := (Nat.card_pos_iff.mp hdegN).2
    obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.exists_chart hx
    let d : K → ℕ := fun _ ↦ 1
    have hd : ∀ k, H.a k = d k := fun k ↦ by simp [hHa, d]
    have hsec := GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial B' x c hc d hd
    have hhom : IsMultiHomog (ι := blockIdx n) (chartMonomial c d) d :=
      (GroundTheory.Heights₂.Heights.geoMultiHomog_iff _ d).mpr
        (GroundTheory.Heights₂.Heights.isWeightedHomogeneous_chartMonomial c d)
    obtain ⟨s, hs⟩ := (ren e).surjective (chartMonomial c d)
    have hsh : IsMultiHomog s d := by
      have h1 : s = ren (fun k ↦ (e k).symm) (chartMonomial c d) := by
        rw [← hs]
        exact ((ren e).symm_apply_apply s).symm
      rw [h1]
      exact homog_ren _ hhom
    have hsW : s ∉ W := by
      rw [← GroundTheory.Heights₂.Heights.mem_map_ringEquiv_iff (ren e), hs, hWx]
      exact GroundTheory.Heights₂.Heights.chartMonomial_notMem_orbitIdeal x c hc d
    have hL : ∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine ι) j) := fun j ↦ j.elim0
    have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) H : Fin 1 → _) = ![H] := by
      funext i
      fin_cases i
      rfl
    have h := hI.2.2 W 0 Fin.elim0 H s d hW hL hH hd hsh hsW
    rw [hsnoc] at h
    have h3 := CoverDenseAlt.heightRecR_full K n (fun _ _ _ ↦ 0) B' x _ hx hsec
    have h4 := recR_map e I (fun _ _ _ ↦ 0) W hW.2.1.2.1 hfin H B'.toGeo s
      (by
        intro t z ht _
        rw [hs, logNorm, logNorm, B'.toGeo.smul t z ht,
          GroundTheory.Heights₂.Heights.eval_smul_of_isMultiHomog _ d hhom t z, norm_mul, norm_prod]
        have hd' : ∀ k, B'.toGeo.a k = d k := hd
        simp only [hd', zpow_natCast, norm_pow]
        rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦
          pow_ne_zero _ (norm_ne_zero_iff.mpr (ht k)))])
      (fun z hz ↦ B'.toGeo_h_of_blockNonzero
        ((GroundTheory.Heights₂.Heights.blockNonzero_unflatCone_iff z).2 hz))
      (by
        rw [hs, hWx]
        exact GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n B' x _ hx hsec)
      (by
        rw [hs, hWx]
        exact fun V hV c₁ c₂ h₁ h₂ ↦ (CoverDenseAlt.chartDehom_full K n B' x _ hx hsec V hV c₁ c₂ h₁ h₂).2)
    rw [hs, hWx, h3, hdeg'] at h4
    have hval : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height I H W =
        GroundTheory.Heights₂.Heights.height B' x := by
      unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height
      rw [h, ← h4, mul_div_cancel_left₀ _ hdeg.ne']
    rw [hval]
    have h1 := hC₁ x hxP
    have h2 : (m : ℝ) * GroundTheory.Heights₂.Heights.height (GroundTheory.Heights₂.Heights.HermLine.standard n) x ≤
        m * C₀ := mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)
    have h5 := le_abs_self (GroundTheory.Heights₂.Heights.height B' x)
    linarith

end PositivityTheory.MbAis.DenseCurves

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiBigTheorem.HSChain
noncomputable section

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter MvPolynomial

theorem hsChain (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.Statement ∧ GroundTheory.Heights₂.Heights.Targets.MoriwakiBigCurve.Statement ∧
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.Statement ∧ GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement ∧
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.Statement := by
  have s1 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof
  have s2 := GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.proof
  have s3 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.proof
  have s4 := GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaSection.proof s1 (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) (GlobalTheory.T.kodaira_generic_of_ample_section_count (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.2) s2 s3
  have s5 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.full
  have s6 := GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.proof
  have s7 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.proof (PositivityTheory.KAmp.kAmp) (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))
  have s8 := GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt.full
  have s9 := GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
  have s10 := GroundTheory.Heights₂.Heights.Kleiman.KHCechDDeg.full
  have s11 := GroundTheory.Heights₂.Heights.Kleiman.KHCechSES.proof s9 s10
  have s12 := GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.full
  have s13 := GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.proof s8 s11 s12
  have s14 := GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubmodules.proof
  have s15 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtChartUnit.proof
  have s16 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtSkyscraper.proof s15
  have s17 := GroundTheory.Heights₂.Heights.HilbertSamuel.LocIdealKer.proof
  have s18 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtFibreLift.proof s14 s11 s16 s17
  have s19 := GroundTheory.Heights₂.Heights.HilbertSamuel.ChartNakayamaGen.proof
  have s20 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearMul.proof
  have s21 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtGenUniform.proof s14 s18 s19 s20
  have s22 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.proof s14
  have s23 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1Vanishing.proof s21 s22
  have s24 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanVarietyH1Generation.proof (PositivityTheory.KAmp.kAmp) s13 s23
  have s25 := GroundTheory.Heights₂.Heights.Kleiman.KHCechMapDeg.full
  have s26 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.proof s11 s25
  have s27 := GroundTheory.Heights₂.Heights.HilbertSamuel.H1GenerationDevissage.proof s8 s11 s12 s26
  have s28 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.full
  have s29 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.proof
  have s30 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeEmbed.full
  have s31 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp.full
  have s32 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep.full
  have s33 := GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full
  have s34 := GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.proof s33
  have s35 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeBadFinite.full
  have s36 := GroundTheory.Heights₂.Heights.Kleiman.KHTheoremSFree.proof s30 s31 s32 s33 s34 s35
  have s37 := GroundTheory.Heights₂.Heights.Kleiman.KHTheoremS.proof s36 s11 s8
  have s38 := GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.proof
  have s39 := GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechComplex.proof
  have s40 := GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechExact.proof
  have s41 := GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.proof
  have s42 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenKoszulStep.proof s39 s40 s41 s9 s10
  have s43 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistVanish.proof s37 s38 s42
  have s44 := GroundTheory.Heights₂.Heights.HilbertSamuel.AmpleOfGenTwist.proof s29 s43
  have s45 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanScheme.proof s24 s27 s28 s44
  have s46 := GroundTheory.Heights₂.Heights.Targets.existsUniqueAll
  have s47 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.proof s45 (fun K _ ι _ => GroundTheory.Heights₂.Heights.geoNumStatement ι) s46
  have s48 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.full
  have s49 := GroundTheory.Heights₂.Heights.HilbertSamuel.G2.proof s4 s5 s6 s7 s47 s48
  have s50 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.proof
  have s51 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.proof
  have s52 := GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.proof
  have s53 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.proof
  have s54 := GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.proof
  have s55 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof s37 s38 s9 s10 s52 s53 s54
  have s56 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.proof
  have s57 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof s51 s55 s56
  have s58 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.full
  have s59 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof s50 s57 s58
  have s60 := GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.proof
  have s61 := GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints.proof
  have s62 := GroundTheory.Heights₂.Heights.AutoClose.Targets_LiftGraphMetric
  have s63 := GroundTheory.Heights₂.Heights.Targets.LiftBlockDatum.proof (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) s60 s61 s62
  have s64 := GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement hResK)
  have s65 := GroundTheory.Heights₂.Heights.Inter.RatR.proof s64
  have s66 := GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance.proof s65
  have s67 := GroundTheory.Heights₂.Heights.HilbertSamuel.AddBlockIsometric.proof
  have s68 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockTop.proof ((GlobalTheory.T.degree_and_coordinates_of_resolution (GlobalTheory.T.resolution_exists_of_resolution_statement hResK)).2) s66 s67
  have s69 := GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.full
  have s70 := GroundTheory.Heights₂.Heights.Targets.LiftCountAlongMultiples.proof s63 s68 (PositivityTheory.LocalParametersCuspidal.MB.HSM.theoremHSMBlock hAIS hResK) s69 (GlobalTheory.T.packing')
  have s71 := GroundTheory.Heights₂.Heights.Targets.AmpleCountAlongMultiples.proofAmple s59 s70
  have s72 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))
  have s73 := GroundTheory.Heights₂.Heights.Targets.NefBigCountAlongMultiples.proof s49 s71 s7 s72 (GlobalTheory.T.packing')
  have s74 := GroundTheory.Heights₂.Heights.Targets.AmpleCountAlongMultiples.statementB s73 (GlobalTheory.T.packing')
  have s75 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.full
  have s76 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanNefF.proof (PositivityTheory.KAmp.kAmp) s75
  have s77 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.full
  have s78 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefPlusAmpleDegree.proof s76 s77
  have s79 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftNefBig.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) s78
  have s80 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.full
  have s81 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftSectionSeparation.proof (hAIS) hDBH s80
  have s82 := GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof
  have s83 := GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof s82
  have s84 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionLatticeFinite.proof s83
  have s85 := GroundTheory.Heights₂.Heights.HilbertSamuel.SeparatedSmallCount.proof s84
  have s86 := PositivityTheory.Pf1.MbRank.ShiftVolumeBound.of_ais s81 s85 (hAIS)
  have s87 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.full
  have s88 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.full
  have s89 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeDegreeZero.proof s74 s79 s86 s87 s88
  have s90 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.proof s74 s89
  have s91 := GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert.proof
  have s92 := GroundTheory.Heights₂.Heights.Targets.CurveSectionQuotFinite.proof
  have s93 := GroundTheory.Heights₂.Heights.Targets.CurveRingFinite.proof
  have s94 := GroundTheory.Heights₂.Heights.Targets.CurveClosedPointChart.proof
  have s95 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointChart.proof s93 s94
  have s96 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointInj.proof s95
  have s97 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointSurj.proof s93 s94
  have s98 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointNagata.proof s95
  have s99 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointMultChart.proof s95 s98
  have s100 := GroundTheory.Heights₂.Heights.Targets.CurveSectionQuotLocal.proof
  have s101 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointLength.proof s95 s96 s97 s99 s100
  have s102 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointResidue.proof s94
  have s103 := GroundTheory.Heights₂.Heights.Targets.CurveVertIndex.proof s92 s101 s102
  have s104 := GroundTheory.Heights₂.Heights.Targets.LocalGenFamily.proof
  have s105 := GroundTheory.Heights₂.Heights.Targets.LocallyPrincipalCoprimeField.proof
  have s106 := GroundTheory.Heights₂.Heights.Targets.InvertibleProductRep.proof
  have s107 := GroundTheory.Heights₂.Heights.Targets.InvertibleIndexCharP.proof
  have s108 := GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMul.proof s104 s105 s106 s107
  have s109 := GroundTheory.Heights₂.Heights.Targets.CurveIndexLinear.proof s93 s94 s108
  have s110 := GroundTheory.Heights₂.Heights.Targets.CurveBoxSmall.proof
  have s111 := GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.proof
  have s112 := GroundTheory.Heights₂.Heights.Targets.CurveFieldNumber.proof s111
  have s113 := GroundTheory.Heights₂.Heights.Targets.CurveEmbedOrbit.proof
  have s114 := GroundTheory.Heights₂.Heights.Targets.ChartLatFull.proof
  have s115 := GroundTheory.Heights₂.Heights.Targets.NumberFieldBoxCount.proof_closed
  have s116 := GroundTheory.Heights₂.Heights.Targets.CurveBoxLattice.proof s112 s113 s114 s115 s84
  have s117 := GroundTheory.Heights₂.Heights.Targets.CurveBoxCount.proof s110 s116
  have s118 := GroundTheory.Heights₂.Heights.Targets.CurveCountLower.proof s91 s103 s109 s117
  have s119 := GroundTheory.Heights₂.Heights.Targets.MoriwakiBigCurve.proof s118 (GlobalTheory.T.packing')
  have s120 := GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.full
  have s121 := GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof s76
  have s122 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleimanLow.proof s120 s121
  have s123 := GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.proof
  have s124 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.full
  have s125 := GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.full
  have s126 := GroundTheory.Heights₂.Heights.HilbertSamuel.G4.proof s90 s125
  have s127 := GroundTheory.Heights₂.Heights.HilbertSamuel.CurveSmallCountLower.proof s91 s103 s109 s117
  have s128 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBigDimensionOne.proof (GlobalTheory.T.packing') s127
  have s129 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeDimensionOne.proof s128
  have s130 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionMixed.proof s126 s129 (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) s78
  have s131 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedSectionStep.proof s130 s65 s120 s121 s124
  have s132 := GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.full
  have s133 := GroundTheory.Heights₂.Heights.HilbertSamuel.FSGeomDegPos.proof (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS) s132
  have s134 := GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSTopPos.proof s133
  have s135 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.full
  have s136 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleimanTop.proof s123 s124 s131 s134 s135
  have s137 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleiman.proof s122 s136
  have s138 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.proof s137
  have s139 := GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaSpan.full
  have s140 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.proof
  have s141 := GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeComplexRadical.proof
  have s142 := GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexMinimalPrimesContract.proof
  have s143 := GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexFormsOnPoints.proof s141 s142
  have s144 := GroundTheory.Heights₂.Heights.HilbertSamuel.IndependentModBaseChange.proof
  have s145 := GroundTheory.Heights₂.Heights.HilbertSamuel.RealFormsOnPoints.proof s143 s144
  have s146 := GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.proof
  have s147 := GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.full
  have s148 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionL2Lattice.proof s140 s145 s146 s147 s3
  have s149 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.full
  have s150 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionRingFinite.proof s84 s149
  have s151 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockVeronese.proof s150
  have s152 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.full
  have s153 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.full
  have s154 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNefGeneric.proof s152 s153 s75
  have s155 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerHeightsirational.proof s154 (GlobalTheory.T.kodaira_generic_of_ample_section_count (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.2) s2
  have s156 := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof
  have s157 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockArith.proof s156
  have s158 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviLogFlat.proof
  have s159 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviHolPerturb.proof
  have s160 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviCompHol.proof
  have s161 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviFSInvariant.proof
  have s162 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.proof s158 s159 s160 s161
  have s163 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.proof s162
  have s164 := GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.full
  have s165 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockPointNorm.proof s140 s164
  have s166 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockOldPartSurj.proof
  have s167 := GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeZariskiDense.proof s143 s141 s142
  have s168 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMeasure.proof s165 s166 s167
  have s169 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockDatum.proof (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) s60 s151 s155 s157 s163 s168
  have s170 := GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.proof
  have s171 := GroundTheory.Heights₂.Heights.HilbertSamuel.TensorPowerL2Degree.proof s169 s68 s170 (PositivityTheory.LocalParametersCuspidal.MB.HSM.theoremHSMBlock hAIS hResK)
  have s172 := GroundTheory.Heights₂.Heights.HilbertSamuel.EuclideanSectionsPower.proof s148 s171
  have s173 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero.proof
  have s174 := GroundTheory.Heights₂.Heights.Targets.SublatticeDegree.full
  have s175 := GroundTheory.Heights₂.Heights.HilbertSamuel.EuclideanSections.proof s172 s173 s174 s139
  have s176 := GroundTheory.Heights₂.Heights.HilbertSamuel.G7.proof s139 s175
  have s177 := GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialShift.proof (GlobalTheory.T.packing')
  have s178 := GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.full
  have s179 := GroundTheory.Heights₂.Heights.HilbertSamuel.UpperNormalisation.proof s176 (GlobalTheory.T.packing') s83
  have s180 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.proof s177 s178 s179
  exact ⟨s90, s119, s138, s176, s180⟩

theorem moriwakiBig_of_classicalTheorems (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  GroundTheory.Heights₂.Heights.Targets.MoriwakiBig.of_found (hsChain hResK hAIS hDBH).1 (hsChain hResK hAIS hDBH).2.1

def HSUse : Prop :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.Statement ∧ GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement ∧
    GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.Statement

theorem hsUse_of_hypotheses (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) : HSUse :=
  (hsChain hResK hAIS hDBH).2.2

end PositivityTheory.Pf1.HilbertSamuelMoriwaki
end
end

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

theorem moriwakiBig_outright : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  moriwakiBig_of_classicalTheorems PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

theorem hsUse_outright : HSUse :=
  hsUse_of_hypotheses PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

end PositivityTheory.Pf1.HilbertSamuelMoriwaki
