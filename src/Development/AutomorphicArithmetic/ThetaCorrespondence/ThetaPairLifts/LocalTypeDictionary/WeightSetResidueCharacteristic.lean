module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesUnitEquiv
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PartialLFunctionOfPublished

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftTestPositiveLevelsKappa
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage3
theorem stage3_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PLevW F ∧ (R.toCx3 F).PartsW false ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  intro P D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM hU hL hPos hK
  obtain ⟨_hGiven, hGS, hCD, hLI, _hTR, _hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨hOk, hGU, hGE, _hBlk, hA, hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hLev : R.PLevW F := GlobalTheory.LevW.levW_of_parts P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hGE hPos hK hA hL hU
  have hW : (R.toCx3 F).PartsW false :=
    GlobalTheory.SumW.partsW_base P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hOk.1 hGE hPos hK hB hU
  obtain ⟨-, hH, hTS, htr⟩ := GlobalTheory.Hk3.HeckeClose.heckeClose P.q1 P.q3 P.q2 R F 1 hT.ok hT.char hT.ex hT.junk hT.ser hT.trSem hU
    hGU hGE hLev hA hB hK hW
  exact ⟨hLev, hW, hH, hTS, htr⟩
end GlobalTheory.Stage3
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pLevW_and_trISep_of_liftTest_pos : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PLevW F ∧ (R.toCx3 F).PartsW false ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  first | exact @_root_.GlobalTheory.Stage3.stage3_alt | exact _root_.GlobalTheory.Stage3.stage3_alt | (intros; apply _root_.GlobalTheory.Stage3.stage3_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalDataSizedFamily
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealDataWeightVectorFamilyCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealDataWeightVectorFamily
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedScalarConjugationInvariance
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.ScalConj.twisted_scalar_conjugation : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.BernsteinZelevinskyFiniteness → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro pI hH pD _ pBZ _ _ pU pW _ D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx hP
  exact GlobalTheory.T.conjugate_baseLevel_of_howeUnramifiedCorrespondence hH T R F κ v₀ O s hOk hsep hC hEx
    (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law GlobalTheory.SingleBlock.localIntegralSingleBlock R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses pD pW pI R.toRealDat F.lv2 hP)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula (GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral) R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue pD pBZ pU R.toRealDat F.lv2)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_scalar_conjugation_invariance : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.BernsteinZelevinskyFiniteness → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  first | exact @_root_.GlobalTheory.ScalConj.twisted_scalar_conjugation | exact _root_.GlobalTheory.ScalConj.twisted_scalar_conjugation | (intros; apply _root_.GlobalTheory.ScalConj.twisted_scalar_conjugation <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage4
theorem stage4_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  intro P hHL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hT hG hM hRow hLv hPos
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  obtain ⟨hOk, hGU, hGE, hBlk, hA, _hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, _hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  obtain ⟨hLevW, hPartsW, hHecke, hSep, _hTr⟩ := _root_.GlobalTheory.T.pLevW_and_trISep_of_liftTest_pos P R F hT hM hG.unif hLT hLv hPos
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL (s := 1) R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hOk.2 hGE hG.unif
  obtain ⟨fw, hBar⟩ := hG.fw
  have hGal : (R.toCx3 F).GalD F.cr false :=
    _root_.GlobalTheory.T.twisted_scalar_conjugation_invariance hE P.q1 P.q2 P.q13 P.q11 P.q9 P.q14 P.q10 P.q7 P.q4 T R F κ v₀ O 1 hT.ok hSep hT.char hT.ex hT.params
      hT.phs hT.std fw hBar hG.ioExt hG.pins (fun i => (hG.oneMap i).1) hG.phase hOk.1 hOk.2 hHecke hGU hGE hBlk hRow hLT hLTB
      hOnto hPos.1 hPos.2 hG.unif hLevW hA hPartsW
  exact ⟨hGal, GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity R F hT.ok hT.char hT.ex hPos hGal hG.unif hLTB hGE⟩
end GlobalTheory.Stage4
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_weight_vector_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  first | exact @_root_.GlobalTheory.Stage4.stage4_alt | exact _root_.GlobalTheory.Stage4.stage4_alt | (intros; apply _root_.GlobalTheory.Stage4.stage4_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneRationalRowsSized
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage2
theorem stage2_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  intro P eps heps
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.definite_positivity_both_levels_short_list P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q12 eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F L hLe hLx hSz hPar hT hM hRow
  obtain ⟨pV⟩ := hPar
  obtain ⟨_hGiven, _hGS, _hCD, _hLI, hTR, hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨_hOk, _hGU, hGE, hBlk, _hA, _hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hPos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos :=
    hx₀ (s := 1) R F L pV hLe hLx hSz hT.ok hT.char hT.ex hT.host hT.ccK hT.guard hT.types hTR hGE hBlk hRow
  have hScal := GlobalTheory.T.thetaLift_positiveScalars_basePlace P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ hGE hPos
  exact ⟨hPos, hScal, GlobalTheory.PrimIn.principalLevel_rows_bijective_of_parts R F hT.ok hT.char hUI hRow hBlk⟩
end GlobalTheory.Stage2
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_bijective_of_multEq : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  first | exact @_root_.GlobalTheory.Stage2.stage2_alt | exact _root_.GlobalTheory.Stage2.stage2_alt | (intros; apply _root_.GlobalTheory.Stage2.stage2_alt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Closing3
theorem primRows3_typesSep3_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → PrimRows3 R F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  intro P hHL eps heps
  obtain ⟨x₀, hx₀⟩ := _root_.GlobalTheory.T.principalLevel_bijective_of_multEq P eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz hPar hT hG hM hRT
  obtain ⟨_hGiven, hGS, hCD, hLI, _hTR, _hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨hOk, hGU, hGE, _hBlk, hA, hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hPos, hK, hH2⟩ := hx₀ R F L hLe hLx hSz hPar hT hM hRT
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  obtain ⟨_hLev, _hW, hHk, hTS, htr⟩ := _root_.GlobalTheory.T.pLevW_and_trISep_of_liftTest_pos P R F hT hM hU hLT hPos hK
  obtain ⟨hGal, hPP⟩ := _root_.GlobalTheory.T.real_data_weight_vector_family_alt P hHL T R F κ v₀ O hT hG hM hRT hPos hK
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  have hPrim := GlobalTheory.primRows3_of_parts P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hOk.1 hOk.2 hHk hGU hGE hRT hLT hLTB
    hOnto hPos hPP hH2 hB hU hML hA hGal
  exact ⟨hPrim, hTS, htr⟩
end GlobalTheory.Closing3
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_weight_vector_family_core_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → PrimRows3 R F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  first | exact @_root_.GlobalTheory.Closing3.primRows3_typesSep3_alt | exact _root_.GlobalTheory.Closing3.primRows3_typesSep3_alt | (intros; apply _root_.GlobalTheory.Closing3.primRows3_typesSep3_alt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
theorem GlobalTheory.PrimIn.holds_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  intro hP hHL eps heps
  obtain ⟨x₀, hx⟩ := _root_.GlobalTheory.T.real_data_weight_vector_family_core_alt hP hHL eps heps
  refine ⟨x₀, ?_⟩
  intro X px I hX Tw Wt z L hLe hx0 hS hPar hB hG hM hRT hI
  have h := hx z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L hLe hx0 hS hPar hB hG hM hRT
  obtain ⟨hcore, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hB.char hB.ex
  have hschur := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 z.R.toRealDat
  obtain ⟨fw, hbar⟩ := hG.fw
  have hconj := GlobalTheory.T.algebraicForm_norm_eq_at_conjugateEmbedding z.core z.R.toRealDat z.F.lv2 z.geo.κ z.geo.v₀ hcore hschur fw hbar hG.unif
  have hlev : z.R.toRealDat.LLevelW z.F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hB.ok.ok2.irr hG.unif hB.char.base.models.HW
  exact ⟨h.1, ⟨hB.ex, hconj, hlev, hI⟩, hB.ok, h.2.1⟩
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_data_sized_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  first | exact @_root_.GlobalTheory.PrimIn.holds_of_ties_alt | exact _root_.GlobalTheory.PrimIn.holds_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimIn.holds_of_ties_alt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.AtDatumEvaluation
open GlobalTheory.Mem.Top.GroupRetwisting
set_option maxHeartbeats 2000000 in
theorem atDat_holds_alt (hP : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hL : GlobalTheory.Published.HeckeLPartialContinuation) :
    AtDat fun _ _ _ _ _ _ _ _ z => GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) →
      GlobalTheory.Mem.R3.Holds z.R z.F := by
  have e1 := (evG_of_ev (ev_scale (_root_.GlobalTheory.T.rational_data_sized_family_alt hP hL))).inter
    ((evG_of_ev LedRec.ev_exists_sizeData).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev))
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  have s2 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (q := fun _ => CoverAt.WeberLev) (evG_all CoverAt.lg_weberLev)
  refine (s1.and (s2.and (Step.and (lUnif_atDat hP.q3 hP.q2 hP.q1) (atDat_lIntegral hP.q3 hP.q2 hP.q1)))).trans
    (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨x₀, hx, hH⟩, hLed, hHost⟩ B f T hO - - ⟨hOk, hW, hU, hI⟩ w hw Z hX Wt z g1 g2 hEx g4 hM hR
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hP.q12 (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz, hpar, hn⟩ := hLed (w.st Z') hO hη hA
  obtain ⟨hhost, -, -, -, -, -, hV, -⟩ := hHost (w.st Z') hO
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  refine _root_.GlobalTheory.Mem.R3.DatCopy.holds_of_copy Z' s (z := z) ?_
  have hEx' := DatCopy.copy_exAt Z' s hEx
  have hU' := DatCopy.copy_lUnif Z' s (hU w hw Z hX Wt z g1 g2 hEx g4)
  have hI' := DatCopy.copy_lIntegral Z' s (hI w hw Z hX Wt z g1 g2 hEx g4)
  have hM' := DatCopy.copy_multEq Z' s hM
  have hR' := DatCopy.copy_rowTest Z' s hR
  generalize DatCopy.copy Z' s z = y at hEx' hU' hI' hM' hR' ⊢
  have hch := y.pins.char
  have hT : TypesTrue (w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
    rw [y.lev.C, w.C_eq]
    exact g1'
  have hIo : IoExt y.R.toRealDat := GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames _ _ _ _ _ _ _ y.R y.F hch hEx' hV
  have hOM : ∀ i, OneMapRowR y.core y.R.toRealDat y.geo.κ y.geo.v₀ y.geo.O (fun _ => 1) i := fun i =>
    GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ y.core y.R y.F y.geo.κ y.geo.v₀ y.geo.O (fun _ => 1) hn hch hEx' ⟨y.geo.fw⟩ hIo i
      (y.geo.pins i) (y.geo.phase i hU')
  exact hH (w.st Z') w.px w.I hX T Wt y L (by rw [hsc]) (by rw [hsc]; exact hx) hsz hpar
    ⟨(hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ y.Xg y.tr y.good.irr, hch, hEx', hhost, ⟨L, hpar⟩, B.ccK_top, y.pins.keep.guard,
      GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT, serClause_of_typesTrue hP.q12 _ hT,
      GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, y.pins.trSem, y.pins.keep.std, y.pins.phs, hn⟩
    (TiesG.of_dat y hU' hIo hOM (CoverAt.coverField_of_weberLev hW w Z' hX Wt y)) hM' hR' hI'
theorem w_of_multEq_and_test_at_weights : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → GlobalTheory.CuspMult.MultEq z.R.toRealDat ∧ Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → WeightCaseCondition := fun hP hL H =>
  (StepW.and H ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans (_root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.atDat_holds_alt hP hL))).trans
    (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v =>
      G.2 Z hX Wt z a b c d (G.1 Z hX Wt z a b k c d e g u v).1 (G.1 Z hX Wt z a b k c d e g u v).2)
end GlobalTheory.Mem.R3.Rw.AtDatumEvaluation
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
theorem _root_.GlobalTheory.T.w_of_weight_residue_char : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → GlobalTheory.CuspMult.MultEq z.R.toRealDat ∧ Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → WeightCaseCondition := by
  first | exact @_root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights | exact _root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights | (intros; apply _root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights <;> assumption)
end
