module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsCompletelyTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunModelArch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGalois
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
namespace GlobalTheory.ExpTie
theorem smallSt_alt : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  unfold _root_.GlobalTheory.ExpTie.SmallnessCondition _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Closed.of_all fun Fm CH => ?_
  refine _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ => ?_
  intro j P W hD hN w _ hWR
  have hC := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hR.ok hR.sep p.charW hR.prim
  have hst := DefFam3.toSub2_stable hC.stable
  have hin := DefFam3.toSub2_inBlock hR.prim.block
  refine ⟨Formalism.EigenvalueLevelCeiling.plc_prime w, ?_, ?_, fun k => DefFam.stable_lifts hst j _ k, DefFam.inBlock_lifts hin j _⟩
  · exact (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds P hN.1 hN.2.1 _ hWR.1).2.2.2.2.2.1
  · refine UpperTheory.ExcSet.not_dvd_discr _ (Formalism.EigenvalueLevelCeiling.plc_prime w) ?_
    rw [← hD.special]
    exact hWR.2.2.2
end GlobalTheory.ExpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptEx
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp.Adapt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp.Adapt
open GlobalTheory.BigOn.Exp.Adapt in
theorem GlobalTheory.BigOn.Exp.adaptEx_alt : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProj
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
noncomputable section
open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion
namespace GlobalTheory.BigOn.Exp.ProjRd
attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK
end GlobalTheory.BigOn.Exp.ProjRd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BigOn.Exp.canProj_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ w _ j rd hrd y => ?_⟩⟩
  obtain ⟨-, -, -, hid, -⟩ := p.grpRecPin
  exact GlobalTheory.BigOn.Exp.ProjRd.rd_eOp (Fm.ex x hx i).nch_tie (p.R.eG.trans p.cG) p.Sx ((j : ℕ) + 1) ((R2 p).FW j)
    (p.nexp.fi j) (GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)) (p.nexp.geq j) (p.nexp.rho _ (Nat.le_add_left _ _) j.2) (p.nexp.chi _ (Nat.le_add_left _ _) j.2)
    (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2) (p.nexp.act _ _ _ (Nat.le_add_left _ _) j.2)
    (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    (fun g => (Fm.D x i).what₂.embLL.injective ((hid g).trans ((Fm.D x i).nStage_trivialCharacter_coeff_eq _).symm)) rd hrd y
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdm
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
namespace GlobalTheory.TwistChr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
theorem twChr_of_twAdm_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩
end GlobalTheory.TwistChr
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem canEx_holds_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalExists :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOf
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpTie.Asm
open _root_.Formalism.L2.Indef _root_.Formalism.L2.Indef.Tree
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem expSt_of_alt : Formalism.CohomologicalDescent.E.ExCut → _root_.GlobalTheory.ExpTie.NumStAlt → _root_.GlobalTheory.ExpTie.ExponentSumStatement → _root_.GlobalTheory.ExpTie.ModelStatement → _root_.GlobalTheory.BigOn.ExponentStatement := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'
end GlobalTheory.ExpTie.Asm
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStOfShareWSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.Comparison₂
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Tied
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → OnTies.RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}
variable {P : Type} [Group P] [Finite P]
end Tied
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.ShareOn.Comparison₂
namespace GlobalTheory.ShareOn
theorem shareSt_of_shareWSt_alt : _root_.GlobalTheory.ShareOn.SharedWeightStatement → _root_.GlobalTheory.BigOn.ShareStatement := by
  intro h
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at h
  unfold _root_.GlobalTheory.BigOn.ShareStatement _root_.GlobalTheory.BigOn.ForallRecordObjects
  refine Closed.imp h fun Fm CH _ H => ⟨0, fun c _ _ => ?_⟩
  obtain ⟨x0, hx0⟩ := H
  exact ⟨x0, fun x hx hle i p hp hm r O hR =>
    Comparison₂.leafShareI_of_shareW p hR (hx0 x hx hle i p hp hm r hR.1.ok hR.2)⟩
end GlobalTheory.ShareOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimesGtThreeR
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.BigOn
theorem typePrimes_gt_three_r_alt :
    _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k
end GlobalTheory.BigOn
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and _root_.GlobalTheory.ShareOn.p0_extreme_or_archOn_of_runModel _root_.GlobalTheory.BigOn.typePrimes_gt_three_r_alt) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩
end GlobalTheory.ShareOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdm
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem recSide_of_twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  intro hA
  refine Formalism.MainNotions.Closed.imp hA fun Fm CH _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p hr hm w hw j Z hRat => ?_⟩
  obtain ⟨hOK, -, -⟩ := H x hx h0 i p hr hm w hw j
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hU : p.R.toRealDat.LUnif := hL.2.2.1
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have T := Z.tie ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hAR := GlobalTheory.SeriesTie.actRead_realRd _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ Z.ρ Z.good
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) Z.pin hU hW
  have hS : Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun a => hr.ties.data _ j _ a fun u => ?_
    have hm0 := GlobalTheory.ExportType.thetaSeriesDatum_mem_levelTypeForms T hAR a
    exact sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hm0 u))
  have hb : baseSet (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) =
      Set.range ((Fm.D x i).nexp.th ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) :=
    (range_th T).symm
  have ht : (⋃ a ∈ Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1)
        ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) =
      twSet Z.good (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) ((Fm.ex x hx i).nch.k' w)
        ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) := by
    rw [hS, Set.biUnion_univ, iUnion_thPsi T hOK]
    ext y
    exact ⟨fun ⟨s, h, P, hd, _, hy⟩ => ⟨s, h, P, hd, hy⟩, fun ⟨s, h, P, hd, hy⟩ => ⟨s, h, P, hd, hRat.1 s h P hd, hy⟩⟩
  refine ⟨?_, ?_⟩
  · unfold baseLat
    rw [hb, hS, Set.image_univ, ← Set.range_comp]
    rfl
  · unfold twLat
    rw [ht]
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFrames
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atPts_and2_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (h' : _root_.GlobalTheory.BigOn.AtPtsAlt Q') : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (Closed.and h h') fun _ _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm => ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm,
      hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩
theorem atPts_mono_of_more {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), More p →
      Q Fm x hx i p → Q' Fm x hx i p) : _root_.GlobalTheory.BigOn.AtPtsAlt Q' :=
  Closed.imp h fun Fm _ _ H => by
    obtain ⟨a, ha⟩ := H
    exact ⟨a, fun x hx hle i p hp hm => f Fm x hx i p hm (ha x hx hle i p hp hm)⟩
open Classical in
set_option maxHeartbeats 1600000 in
theorem modelSt_of_small_frame_gal : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' →
    _root_.GlobalTheory.ExpTie.GaloisStatement → _root_.GlobalTheory.ExpTie.ModelStatement := by
  intro hBS hCheb hS hFr hGal
  refine _root_.GlobalTheory.ExpModel.atPts_mono_of_more (_root_.GlobalTheory.ExpModel.atPts_and2_alt hS (_root_.GlobalTheory.ExpModel.atPts_and2_alt hFr hGal)) ?_
  intro eps Fm x hx i p _ H j P W hD hN w hw hR
  obtain ⟨hs, hf, hg⟩ := H
  have hsm : SmallAt p j P w := hs j P W hD hN w hw hR
  haveI hl : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hsm.1⟩
  obtain ⟨F, R, inc, hFok, ⟨T⟩⟩ := @hf j P W hD hN w hw hR hl
  have hG := @hg j P W hD hN w hw hR hl F R inc hFok T
  have hNr := hN.1.Nr_eq
  have ht := hN.1.t_ge
  have hl2 : Formalism.EigenvalueLevelCeiling.plc w ≠ 2 := by have := hsm.2.1; omega
  obtain ⟨fr, cjj, hlk⟩ := GlobalTheory.T.crystallineLatticeLink_of_blockData hBS _ (AlgebraicClosure (Fm.D x i).host.E) (Formalism.EigenvalueLevelCeiling.plc w) hl2 hsm.2.2.1 _ inc T.half
  obtain ⟨jK, hJ⟩ := GlobalTheory.ExpFrame.levelMap_exists (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam
  obtain ⟨_, _, hH⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam jK hFok hJ (NablaT F.O P.Nr W.lam)
  refine ⟨fr, cjj, {m : MaximalSpectrum F.T // ∃ θ, R.Occurs (subZ p j (p.R.mu w)) θ ∧ F.Over θ m.asIdeal},
    fun m => haveI := m.1.isMaximal.isPrime; F.setting W.lam jK m.1.asIdeal, ?_, ?_⟩
  · exact GlobalTheory.T.maximalIdeals_meeting_subspace_cover _ _ _ (blk p j (p.R.mu w)) w _ P.Nr F W.lam jK hFok hJ hH R (lvlL p) _ hsm.2.2.2.1
  · rintro ⟨m, θ0, hocc, hov⟩
    have hop : ∀ Q, (blk p j (p.R.mu w)).op (Q, 0) = 1 := fun Q => (p.charW.base.fam.degL j (p.R.mu w) Q).1
    obtain ⟨hb, he⟩ := GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part _ _ _ (blk p j (p.R.mu w)) w (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam R _ hop hsm.2.2.2.2 θ0 hocc
    exact ⟨GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok, winputs_frame _ (AlgebraicClosure (Fm.D x i).host.E) hCheb (Formalism.EigenvalueLevelCeiling.plc w) _ inc fr cjj P W hN.2.2.1
      (hlk P W hN.1 hN.2.2.1 hD.box) F hFok R.HasBlock hG jK hJ hH (GlobalTheory.T.finite_frameCoeffRing_quotient_prime _ _ _ F hFok) (GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok) m.asIdeal θ0 he hb hov⟩
end GlobalTheory.ExpModel
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FockVecEqSum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FockVecEqSum
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FockVecSum
theorem fockVec_eq_sum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H], ∃ κ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q, pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ • ((_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ p, 1)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj _
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hj' : j < D.R.m := Nat.lt_of_succ_lt hj
  have hlift := GlobalTheory.ChainEquiv.lifts_chain (_root_.GlobalTheory.Fam.pk_z W).toLevCh W.P.A3.A.μ0 hL t j hj'
  choose κ hκ using fun p : (_root_.GlobalTheory.Fam.complexLevelStructure W).H => hlift p.1
  refine ⟨κ, fun p => ⟨(hκ p).1, (hκ p).2.1, (hκ p).2.2 ▸ p.2⟩, fun v hv Q => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hL t ⟨j, hj'⟩
  obtain ⟨c, hc⟩ := hL.βY j hj'
  obtain ⟨c', hc'⟩ := hL.βY (j + 1) hj
  have hω := hC.chain.ωY t j hj
  have hvY := hC.chain.vY t j hj
  have hsum := GlobalTheory.StepVecSum.stepVec_eq_sum D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) v hω
    (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY j))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hj'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (j + 1) hj)) hc.1 hc'.1 D.R.r D.R.t j (r_le_Y j)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D _ _ _ hL t).1 (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) (_root_.GlobalTheory.Fam.complexLevelStructure W) hvY hv
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvY.1.2.inf
  have hf : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) := by
    have := hC.chain.ptY t j hj 1
    rwa [RealDat.ptY, GlobalTheory.FiniteFock.pureTensorO_one] at this
  rw [hsum, GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ _ _ _ _ Finset.univ _ _ (fun p _ => hω.om_pres _ _ hf)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hk := GlobalTheory.FiniteFock.compAt_mt_of_finite (_root_.GlobalTheory.Fam.pk_z W).θ
  refine ((GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hω hθ _ _ _ _ _ _ _ _ (κ p) 1
    (fun τ => by rw [hk τ (hκ p).1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (hκ p).1, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.one_mul]) _ hf Q).2).symm
end GlobalTheory.FockVecSum
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FockVecEqSumStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_elements_step_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H], ∃ κ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q, pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ • ((_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ p, 1)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) := by
  first | exact @_root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt | exact _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt | (intros; apply _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadStOfBadW
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.BadOnRec
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}
end General
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] runAlgBad
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem bad_rec_alt (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O) {del : ℝ} (j : Fin D.R.m) (hbad : BadW p j del) :
    (1 - del) * O.d0 j ≤ ((S2 p).D : ℝ) := by
  obtain ⟨hC, hOk, -, -, hRk, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  letI : Algebra (r.used v₁).full.J.Q.c.F D.what₂.LL := p.alg
  have hmem := mem_eig_iff (ht v₁ j).1 (ht v₁ j).2 hC.grp hU
  have hf := finrank_eq_of_bij _ (GlobalTheory.OnTies.toForms_bijective (hrec.1.ok.laws v₁).p (fw2 p) j (z j)) _ _ hmem
  have hd0 : O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) : ℝ) := by
    unfold OnObj.d0
    exact congrArg (fun n : ℕ => (n : ℝ)) hf
  have hV : ∀ x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j, goodOp (R2 p) j x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j :=
    fun x hx g => by
      rw [← GlobalTheory.BigOn.goodOp_rho_comm hOk.irr j (g : p.P.Gp) x, hx g, map_smul]
  have hsplit := finrank_inf_range_add_inf_ker (goodOp (R2 p) j)
    (fun x => LinearMap.congr_fun (goodOp_idem hOk.irr j) x) _ hV
  have hD : (S2 p).D = finrank D.what₂.LL ((R2 p).WL (F2 p) false j) := (hRk.2 j).symm
  have hbad' : (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) :
      Submodule D.what₂.LL _) : ℝ) ≤ del * finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := hbad
  have hs : (finrank D.what₂.LL ((R2 p).WL (F2 p) false j) : ℝ) +
      (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) : Submodule D.what₂.LL _) : ℝ) =
      finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := by
    exact_mod_cast hsplit
  rw [hd0, hD]
  nlinarith
end Point
end GlobalTheory.BadOnRec
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem badSt_of_badW_alt : _root_.GlobalTheory.ShareOn.BadWeightStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement := by
  intro hB
  refine (hB.and GlobalTheory.T.badShareSize_bounds_along_family).imp fun Fm CH _ H => ?_
  obtain ⟨⟨x1, H1⟩, ⟨x2, H2⟩⟩ := H
  refine ⟨0, fun c _ _ => ⟨max x1 x2, fun x hx hle i p hR hm r O hrec => ?_⟩⟩
  have hb := H1 x hx ((le_max_left _ _).trans hle) i p hR hm r hrec.1.ok hrec.2
  have hq := (H2 x hx ((le_max_right _ _).trans hle) i).2.2.1
  intro j
  exact ⟨_, (Real.exp_pos _).le, hq, _root_.GlobalTheory.BadOnRec.bad_rec_alt hR hm hrec j (hb j)⟩
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemS
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemS
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem under_mem_S_alt {W : _root_.GlobalTheory.MiS.RealPackAlt ex} (hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (_root_.GlobalTheory.BaseChain.com_z W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (_root_.GlobalTheory.Fam.pk_z W).C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (hL.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (hL.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]
theorem stage_y_is (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) (hj : j < D.R.m) :
    (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Is (_root_.GlobalTheory.BaseChain.com_z W) j := by
  have hC := hP.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hM : (_root_.GlobalTheory.Fam.pk_z W).IsModels := hC.models
  have hQ := _root_.GlobalTheory.BaseChain.Q_base_eq_empty W
  have hm : min j D.R.m = j := min_eq_left hj.le
  obtain ⟨c, hc⟩ := hL.βY j hj
  have hν : ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) ((_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j) := by
    by_cases h1 : j + 1 < D.R.m
    · exact ⟨(hM.νY _ j h1).1.1, (hM.νY _ j h1).2⟩
    · have : j = D.R.m - 1 := by omega
      subst this
      exact ⟨(hM.νY' _).1.1, (hM.νY' _).2⟩
  haveI := hν.1
  refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [D.sp.Y_rank _ (min_le_right _ _), hm]
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [D.Y_sigval _ (min_le_right _ _), hm]
  · show parB _ (min j D.R.m) = _
    rw [hm]
  · push_cast at hN
    have := P.isPrime.mem_of_pow_mem _ hN
    rcases P.isPrime.mem_or_mem this with h0 | h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 0 P h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 1 P h0
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [hQ]; rfl
  · exact (MeasureTheory.Measure.IsHaarMeasure.smul _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W) :
      (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure)
  · exact hν.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemSStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Is (_root_.GlobalTheory.BaseChain.com_z W) j := by
  first | exact @_root_.GlobalTheory.BaseChain.stage_y_is | exact _root_.GlobalTheory.BaseChain.stage_y_is | (intros; apply _root_.GlobalTheory.BaseChain.stage_y_is <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFam
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFam
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ColMatchFam
theorem col_level_match_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.LevTraceAlt f B → B.Adapted (W.S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ x ∈ GfC (D.sp.X 0), ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) ∈ rowJ W.S.X W.Q.instEq) ∧ ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))) = _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B hLev hAd a₀ hH0 b hb
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  have hLM := hP.bot.hyp.2.1 u
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl b
  obtain ⟨hU, hchi⟩ := hLev b hb y hy.symm
  have hgf : a₀ * b * a₀⁻¹ ∈ GfC (D.sp.X 0) := mul_mem (mul_mem hH0.1 hb) (inv_mem hH0.1)
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D W.S.X W.Q.instEq u W.Q.Rl.ψ B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hE hAd (a₀ * b * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hh0 : (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    GlobalTheory.ColMatch.unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one a₀ _ (by rw [e0]; exact hh0)
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * b * a₀⁻¹) =
      (((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF W.S.X (W.S.tr u).wt (W.S.tr u).ιA ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf)
      ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) := by
    have h := hRep
    rw [hfg] at h
    exact h
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 (B.toH (a₀ * b * a₀⁻¹)).2 _ hRF
  have hconj : (W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 = y := by group
  have hfinE : embA B.d B.o (a₀ * b * a₀⁻¹) ∈ GfC (D.sp.Y 0) := GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o hgf
  have hfst : (iotaX W.S.X W.Q.instEq (embA B.d B.o (a₀ * b * a₀⁻¹))).1 = 1 :=
    GlobalTheory.Core.Mi.CenAct.iotaX_fst W.Q.instEq hfinE
  have hio : iotaX W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) =
      (1, (W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := by
    rw [map_mul, map_mul, map_inv, (iotaX W.S.X W.Q.instEq).apply_symm_apply]
    ext
    · simp only [Prod.fst_mul, Prod.fst_inv, hfst, mul_one, inv_one]
    · rfl
  have hrow : ∀ k, k ∈ rowJ W.S.X W.Q.instEq ↔
      (iotaX W.S.X W.Q.instEq k).1 = 1 ∧ (iotaX W.S.X W.Q.instEq k).2 ∈ W.S.X.K2 := fun k => Iff.rfl
  have hU' : ∀ hyU : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U,
      ((((W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 :
        Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
          GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U) := fun hyU => by rw [hconj]; exact hyU
  refine ⟨⟨fun hk => ?_, fun hr => ?_⟩, fun hk => ?_⟩
  · have hm := hmemIff.2 (hU' (hU.2 hk))
    rw [hrow, hio]
    exact ⟨rfl, hm⟩
  · rw [hrow, hio] at hr
    have h2 := hmemIff.1 hr.2
    rw [hconj] at h2
    exact hU.1 h2
  · have hyU := hU.2 hk
    have hm := hmemIff.2 (hU' hyU)
    have hp := hpsi hm (hU' hyU)
    have hc := hchi hyU
    have hchieq : (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hU' hyU⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
      have key : ∀ (z : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hz : z.1 ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), z = y →
          (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hz⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
        rintro z hz rfl
        rfl
      exact key _ _ hconj
    unfold rowChi
    rw [hio]
    have hpv : ((psiK W.S.X u _ ⟨_, hm⟩ : ℂˣ) : ℂ) =
        W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := rfl
    have hn : ‖W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u)‖ = 1 :=
      W.S.Y.hK.2.2.2.2 _ hm
    have h1 : W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) *
        _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1 := by
      rw [← hpv, hp, hchieq]
      exact hc
    generalize W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) = c at hn h1 ⊢
    generalize _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = L at h1 ⊢
    have hsc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]
      simp
    calc star c = star c * (c * L) := by rw [h1, mul_one]
      _ = (star c * c) * L := by ring
      _ = L := by rw [hsc, one_mul]
end GlobalTheory.ColMatchFam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFamStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_trace_adapted_translate_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.LevTraceAlt f B → B.Adapted (W.S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ x ∈ GfC (D.sp.X 0), ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) ∈ rowJ W.S.X W.Q.instEq) ∧ ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))) = _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0))) := by
  first | exact @_root_.GlobalTheory.ColMatchFam.col_level_match_fam_alt | exact _root_.GlobalTheory.ColMatchFam.col_level_match_fam_alt | (intros; apply _root_.GlobalTheory.ColMatchFam.col_level_match_fam_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoLevChi
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoLevChi
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepLevelP.IoLevPf
end GlobalTheory.StepLevelP.IoLevPf
namespace GlobalTheory.StepLevelP
set_option maxHeartbeats 800000 in
theorem io_levChi_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ F : (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1), F.1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) (g * κ) = levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) g := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF κ hκ φ x g
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).Is W.P.A3.A.μ0 := hC.lev
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have hio := hC.chain.ioY t j (by omega)
  have hκG : κ ∈ GfC (Yc D j) := hκ.1
  have hκP : Lev.finE (Yc D j) κ ∈ parLev D.sp.cm (Yc D j).gram ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) := hκ.2.1
  have hκH : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ) ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := hκ.2.2
  have hκl : IsLevelLift (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)
      (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ)) κ := ⟨hκG, hκP, rfl⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain (_root_.GlobalTheory.Fam.pk_z W) hL t (j + 1) hj
    (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ))
  have hj' : j < D.R.m := by omega
  have hlaw := GlobalTheory.StepLaw.step_law (_root_.GlobalTheory.Fam.pk_z W).toLevCh hL t j (j + 1) rfl hj' hθ (D.sp.Y_sig _) (D.sp.Y_sig _) (r_le_Y _) (r_le_Y _)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY j hj') (hL.βY (j + 1) hj)
    (hC.chain.ωY t j hj) (hC.chain.vY t j hj) _ κ κ' hκl hκ'
  have hsS : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' ≠ 0 :=
    levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ)⁻¹ •
      (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).vY t j := hlaw
  have hv : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ *
        (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) •
        (_root_.GlobalTheory.Fam.pk_z W).vY t j := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) hθ (hC.chain.ωY t j hj)
    _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vY t j) (hC.chain.ptY t j hj) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (hC.chain.ωY t j hj)
    ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) (hC.chain.ptY t j hj φ)
  have hκ'H : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D (j + 1)) κ') ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := by
    rw [hκ'.2.2]; exact hκH
  have hκ'P : κ' ∈ levS (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) := ⟨hκ'.1, hκ'.2.1, hκ'H⟩
  have e1 : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hsub : (⟨_, hκ'H⟩ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H) = ⟨_, hκH⟩ := Subtype.ext hκ'.2.2
  have e2 : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ' =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) *
        levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκ'H, Units.val_mul, hsub]
    rfl
  have hfd : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have := hC.models.νY t (j + 1) h
      exact ⟨this.1.1, this.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      rw [e]
      have := hC.models.νY' t
      exact ⟨this.1.1, this.2⟩
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Yc D (j + 1))
  have htg : IsTopologicalGroup (GA D (Yc D (j + 1))) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Yc D (j + 1)).gram))
  haveI := hfd.1
  haveI hR : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) = (_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) := map_mul_right_eq_self _ κ'
  have hFv := fun v => GlobalTheory.StepLevelP.IoLevPf.multT_val (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) _ _ F.1 hF v
  have hpt' : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) = (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) • (_root_.GlobalTheory.Fam.pk_z W).ptY t j φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1))
    ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) hfd.2 κ' hmap
    (fun h => thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D j)).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, (hFv x).1 γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) (h * κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x (h * κ') =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ * levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ') * (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h) := fun h => by
    rw [hth, (hFv x).2 κ' hκ'P]; ring
  rw [← hio.eq F φ x (g * κ), ← hio.eq F φ x g]
  unfold Lift.liftInt
  rw [← hint.2]
  simp only [hpw]
  rw [integral_const_mul, e1, e2]
  field_simp
end GlobalTheory.StepLevelP
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoLevChiStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_projection_level_character_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ F : (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1), F.1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) (g * κ) = levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) g := by
  first | exact @_root_.GlobalTheory.StepLevelP.io_levChi_alt | exact _root_.GlobalTheory.StepLevelP.io_levChi_alt | (intros; apply _root_.GlobalTheory.StepLevelP.io_levChi_alt <;> assumption)
end
end
end
