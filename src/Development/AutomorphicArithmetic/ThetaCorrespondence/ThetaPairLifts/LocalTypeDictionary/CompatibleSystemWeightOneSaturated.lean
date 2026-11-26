module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineAdelicDatumOfPublishedStatementsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeightSetResidueCharacteristic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBareFormOfSaturation
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoldsOfMultiplicityEqual
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoldsLOfTies
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn GlobalTheory.LiftRows
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.LiftsOnly
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
section Real
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Real
set_option maxHeartbeats 1000000 in
theorem holdsL_of_ties_alt (P : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hHL : GlobalTheory.Published.HeckeLPartialContinuation)
    (eps : ℝ) (heps : 0 < eps) : ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
      {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
      (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
      (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
      (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x →
      Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat →
      R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Rw.HoldsL R F := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.LiftRows.goodForms_definite_exist (GlobalTheory.DefFree.goodVectorsDefinite P.q12) eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz ⟨pV⟩ hT hG hM hInt
  obtain ⟨hGiven, hGS, hCD, -, hTR, hUp, -⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨hOk, hGU, hGE, hBlk, hA, hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay P.q2 R.toRealDat
  have hRows : RowsNe R.toRealDat F.lv2 := GlobalTheory.RowsNeProof.rowsNe R.toRealDat F.lv2 1 hT.ok.ok2 hcore.1 hSch R.SF hcore.2.1 hTR
    (hx₀ D L pV hLe hLx hSz R.toRealDat F.lv2 hGiven)
  have hCar := carries_of_upInj P.q2 P.q1 R F hT.ok hT.char hT.ex hT.junk hGE hUp
  obtain ⟨hScal, hMatch, -, -⟩ := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8
    (_root_.ResidueKilled.sec_of_dm P.q9) P.q10 P.q11 R.toRealDat F.lv2 hGiven hT.ccK hT.char.allPl
    (GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex) R.SF hcore.2.1 hTR
  have hK := GlobalTheory.PosAtBase.pos_at_base R F hT.ok hT.char hT.ex hScal hMatch
    (GlobalTheory.CarriesOne.parts_eq_of_carries P.q1 P.q2 R F hT.ok hT.char hT.ex hJ hUp)
    (exists_rowPart_ne_bot_positiveDimension P.q2 R F hT.char hT.ex hCar hRows)
  have hLev := levW_of_span P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hBlk hCar hK hA hLT hU
  have hW := partsW_of_carried P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hOk.1 hCar hK hB hU
  obtain ⟨-, hH, hTS, -⟩ := GlobalTheory.Hk3.HeckeClose.heckeClose P.q1 P.q3 P.q2 R F 1 hT.ok hT.char hT.ex hT.junk hT.ser hT.trSem hU
    hGU hGE hLev hA hB hK hW
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  obtain ⟨fw, hbar⟩ := hG.fw
  have hConj : R.toRealDat.PConj := GlobalTheory.ConjNorm.pConj T R.toRealDat F.lv2 κ v₀ hcore.1 hSch fw hbar hU
  have hLW : R.toRealDat.LLevelW F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hT.ok.ok2.irr hU hT.char.base.models.HW
  exact ⟨hOk.1, hOk.2, hH, hGU, hGE, hBlk, hLT, hLTB, hOnto, hU, hML, hLev, hA, hW, ⟨hT.ex, hConj, hLW, hInt⟩, hT.ok, hTS⟩
end GlobalTheory.LiftsOnly
end
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.R3.LiftsAt
open GlobalTheory.Mem.Top.GroupRetwisting
theorem ev_closes_alt (P : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hHL : GlobalTheory.Published.HeckeLPartialContinuation) :
    Ev fun K => ∀ (X : Stages) (L : SizeData₂ X.toD7), L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X := by
  refine ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩
  obtain ⟨x₀, h⟩ := _root_.GlobalTheory.LiftsOnly.holdsL_of_ties_alt P hHL eps h0
  exact ⟨x₀, fun K _ _ _ hs hx X L e hS hP px I hX Tw Wt z =>
    h z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L (by rw [e]; exact hs) (by rw [e]; exact hx) hS hP⟩
set_option maxHeartbeats 4000000 in
theorem lu_of_multEq_at_data : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  intro P hHL hM
  have hE : Step KPx (fun _ _ _ _ => True) fun K B f T => (∀ X : Stages, X.B = B →
      (∀ L : SizeData₂ X.toD7, L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X) ∧
      (X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) →
        ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) ∧
      Formalism.IndefR.Links.HostHyp X.toD7 ∧
      ∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
        (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) :=
    Step.of_evG ((((evG_of_ev (_root_.GlobalTheory.Mem.R3.LiftsAt.ev_closes_alt P hHL)).inter (evG_of_ev LedRec.ev_exists_sizeData)).inter
      (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp fun K _ _ _ _ H B f T hO _ _ _ X e => by
        subst e
        exact ⟨H.1.1 X, H.1.2 X hO, (H.2 X hO).1, (H.2 X hO).2.2.2.2.2.2.1⟩)
  refine ((((hE.and (Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))).and
    (Step.of_evLgG (q := fun _ => CoverAt.WeberLev) (evG_all CoverAt.lg_weberLev))).and hM).and
    (Step.and (lUnif_atDat P.q3 P.q2 P.q1) (atDat_lIntegral P.q3 P.q2 P.q1))).trans
    (Step.of_all fun K B f T _ _ _ H w hw Z hX Wt z g1 g2 hEx g4 => ?_)
  obtain ⟨⟨⟨⟨h1, hOk⟩, hW⟩, hM⟩, hU, hI⟩ := H
  obtain ⟨b, hb, heta, hA⟩ := LedRec.exists_bare P.q12 (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨hcl, hled, hhost, hV⟩ := h1 (w.st b) rfl
  obtain ⟨L, hL, hS, hP, hn⟩ := hled heta hA
  have s : SameGrp (C := w.C) Z b := LedRec.sameGrp g1 hb
  have hEx' := DatCopy.copy_exAt b s hEx
  have hU' := DatCopy.copy_lUnif b s (hU w hw Z hX Wt z g1 g2 hEx g4)
  have hT := ties_at P.q12 w b hX Wt (DatCopy.copy b s z) hb
    ((hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ _ _ (DatCopy.copy b s z).good.irr) hEx' hhost ⟨L, hP⟩ hn
    (GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames _ _ _ _ _ _ _ (DatCopy.copy b s z).R (DatCopy.copy b s z).F (DatCopy.copy b s z).pins.char hEx' hV) hU' hW
  exact LiftCopy.holdsL_of_copy b s (hcl L hL hS hP w.px w.I hX T Wt (DatCopy.copy b s z) hT.1 hT.2
    (DatCopy.copy_multEq b s (hM w hw Z hX Wt z g1 g2 hEx g4)) (DatCopy.copy_lIntegral b s (hI w hw Z hX Wt z g1 g2 hEx g4)))
end GlobalTheory.Mem.R3.LiftsAt
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_of_multiplicity_equal : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  first | exact @_root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data | exact _root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data | (intros; apply _root_.GlobalTheory.Mem.R3.LiftsAt.lu_of_multEq_at_data <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
namespace GlobalTheory.Mem.R3.Rw.Bare
set_option maxHeartbeats 4000000 in
theorem bare_form_saturated : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  intro hA hH hE
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have holdsL : LowerUnitaryCaseCondition := _root_.GlobalTheory.T.lu_of_multiplicity_equal hH.h1 hH.h3 hH.multL
  have datS : DatExS := GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have hW := GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field hH.h1.q12 datS holdsL hE
  have hPr := GlobalTheory.T.constructionStartingChoices_of_fine_adelicData hA.a8 hA.a9 hA.a10 hA.a6 holdsW
  have pS : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have iS : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have s1 : StepW Start fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) := by
    refine (iS.and ((pS.trans hW).and hPr)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
    obtain ⟨⟨hPin, hSupp, -⟩, hU, hP⟩ := h
    by_cases hT : T = TwDat.untw B T.pl
    · obtain ⟨Z, hX, z, g, gr, ga, ka, hF, hsub, hpsi, hsat⟩ := hU hT
      obtain ⟨P, hZ, hWt, -⟩ := hP Z hX z g gr ga ka hF hsub hpsi
      refine ⟨hPin, P, fun _ => ?_⟩
      rw [hWt, hZ]
      exact hsat
    · rcases hSupp with h | hG
      · exact absurd h hT
      obtain ⟨Z, hX, z, g, gr, ga, ka, ex, ig, core, std, hsub, hpsi⟩ := hG
      obtain ⟨P, -, -, -⟩ := hP Z hX z g gr ga ka ⟨ex, ig, core, std⟩ hsub hpsi
      exact ⟨hPin, P, fun h => absurd h hT⟩
  have hQ : StepW (fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt)) (pinAnd HasPk) :=
    StepW.of_all fun _ _ _ _ _ _ _ h => ⟨h.1, ⟨h.2.choose⟩⟩
  refine s1.trans ((StepW.of_all fun _ _ _ _ _ _ _ h => h).and (hQ.trans GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep) |>.trans
    (StepW.of_all fun K B f T w hO _ h => ?_))
  obtain ⟨⟨-, P, hsat⟩, hN⟩ := h
  obtain ⟨N, hEm, hG, hN⟩ := hN P
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk B w.C (Gc B w.px) P.q.p P.q.e P.q.W₀ P.q.n (fun _ _ => 0)
    (fun _ _ => le_rfl) (frames_unit P.q.t) (fun u => ((w.C.fm u).lat 0).L) (fun _ => 0) (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l P.hX) (rows_le P.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hA.a8 hA.a9 hA.a10 hA.a6 K B f T w P ⟨_, _, V, S, N, P.Z₀.G⟩
    ⟨hV, hG, (hN V S P.Z₀.G).1, (hN V S P.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  refine ⟨P, x, hsat, ?_⟩
  exact Eq.mpr (congrArg (fun o : P.q.Over => IsEmpty o.N.nd.Loc ∧ ∀ j v, o.η j v = 0) hx) ⟨hEm, fun _ _ => rfl⟩
end GlobalTheory.Mem.R3.Rw.Bare
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bare_form_of_saturation : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  first | exact @_root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated | exact _root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated | (intros; apply _root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
theorem weightOne_saturated_of_hypotheses : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := fun hA hH =>
  _root_.GlobalTheory.T.exists_bare_form_of_saturation hA hH (GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10)
end GlobalTheory.HeightCounting.Up
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_weightOne_saturated : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | exact _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | (intros; apply _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses <;> assumption)
end
