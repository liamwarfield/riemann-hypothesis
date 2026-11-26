module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatRowTestOfExField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioOfLocalMatchingTowers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorRatioHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open Finset GlobalTheory.FunObj.SqNum
namespace GlobalTheory.RowClaim
set_option maxHeartbeats 1600000 in
theorem twisted_local_factor_ratio_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ConstK →
    GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.TriEx → GlobalTheory.SqTop.Tower → RatioK := by
  intro hP hTA hLM hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hTA hLM hLN
  obtain ⟨c1, h1⟩ := hC
  obtain ⟨c5, h5⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hLN hTX) (GlobalTheory.SqTop.Model.gBig_and hTW hBF)
  refine ⟨max c1 c5, fun ε CF hCF => ?_⟩
  obtain ⟨x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C0, x5, g5⟩ := h5 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x5, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hi hsc => ?_⟩
  have hc := g1 D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hi hsc
  have hrec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hs.size, hs.host⟩
  have hL : R.toLevCh.Is A.μ0 := hs.core.lev
  intro hfield
  obtain ⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := g5 C0 le_rfl D large₂ he (le_of_max_le_right hx) hrec T R.toLevCh A.μ0 hL G
  have hstd : IsStdChar D W.ψ (-1) := (hi.weil.ψ : W.ψ = _) ▸ hs.std
  exact fun i j t => sqRatio_mem_grid G A.μ0 W S.toGridChoice rm c hfield hc hi.const (fun i j => (hLN' i j).1)
    (hTX' W hstd) (hTW' W S.toGridChoice rm hstd hfield) (hBF' W hstd) i j t
end GlobalTheory.RowClaim
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftExtensionFieldExists
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedGridExistenceOfIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open scoped TensorProduct nonZeroDivisors Pointwise
namespace GlobalTheory.RowEx.GridExPf
open _root_.Formalism.L2.Col GlobalTheory.GridPlaces
variable {D : D7}
end GlobalTheory.RowEx.GridExPf
namespace GlobalTheory.RowEx
open GlobalTheory.RowEx.GridExPf
theorem twisted_grid_existence_of_identity (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : GridEx := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS hQ => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS.size
  have hcls : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK := Pm.level_split
  have hPl := exists_places_of_cls T R.toLevCh A.μ0 hS.core.lev (fun k => hcls _ (D.host.g_level k))
    (hcls _ D.host.pde_level.1) (hcls _ D.host.pde_level.2) (leastSplitAuxiliaryPrime_ne_typePrime_of_sizes hS.size) hQ
  obtain ⟨G⟩ := (GlobalTheory.ChiGridModel.nonempty_gridData_iff R.toLevCh A.μ0 hS.core.lev ⟨1, CF, large₂.sc.b⟩).2 hPl
  obtain ⟨W, hW⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hP.weilRepresentationUnitaryPair R hS.core.lev
    hS.core.chain hS.core.models _ G
  haveI := hS.fin
  exact ⟨G, W, hW, GlobalTheory.FunObj.gridChoice_nonempty_of W hS.core.lev Set.finite_univ (GlobalTheory.RowClaim.Test.pde_ne_q hS)
    fun t _ P hP => GlobalTheory.RowClaim.Test.guard hS t P hP⟩
end GlobalTheory.RowEx
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
namespace GlobalTheory.RowEx
theorem exists_extension_field_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField :=
  fun hw hm P hJ ht K WC LM TA FS =>
    exField_of_keyFin_exKey keyFin_holds
      (exKey_of (_root_.GlobalTheory.RowEx.twisted_grid_existence_of_identity P)
        (isEx_of_separates FS (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)) (_root_.GlobalTheory.RowEx.twisted_base_existence P (_root_.GlobalTheory.RowEx.twisted_constant_existence hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P))
          (GlobalTheory.NFJetProof.nfJet_holds (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P) GlobalTheory.NormSum.inp_all (_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large P GlobalTheory.NormSum.inp_all))
          (_root_.GlobalTheory.RowEx.RatioField.twistRatio_mem_numberField P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (_root_.GlobalTheory.RowEx.bottomField_isNumberField P GlobalTheory.NormSum.inp_all))
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds)
end GlobalTheory.RowEx
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_extension_field_exists : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField := by
  first | exact @_root_.GlobalTheory.RowEx.exists_extension_field_of_join | exact _root_.GlobalTheory.RowEx.exists_extension_field_of_join | (intros; apply _root_.GlobalTheory.RowEx.exists_extension_field_of_join <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
theorem GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun sg hw g P hJ a12 K LM T3 =>
    have s1 := _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence sg P
    have s2 := _root_.GlobalTheory.SquareLM.twisted_square_local_matching hw P K LM
    have s3 := _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree P K LM
    have j := _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj P K LM s1 s2 s3
    have l := GlobalTheory.SqTop.lNe_of_functionalEquation a12.abs GlobalTheory.HeckeStrip.completedLBoundedInStrips GlobalTheory.SqTop.fieldDat
    GlobalTheory.Twist.atDat_rowTest_of_exField g P.cuspRapidDecay j.2.2.1
      (GlobalTheory.RowEx.injK_of_separates_linB T3 (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)))
      j.2.1 j.1 j.2.2.2.1 j.2.2.2.2
      (_root_.GlobalTheory.RowClaim.twisted_local_factor_ratio_holds P K LM j.2.1 l (_root_.GlobalTheory.SqTop.triEx_holds_alt hw P K LM l) (_root_.GlobalTheory.SqTower.tower_alt_bis P K LM l))
      (_root_.GlobalTheory.T.theta_lift_extension_field_exists hw LM P hJ a12 K s1 s2 s3 T3)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_vector_assembly_holds : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  first | exact @_root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | exact _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | (intros; apply _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join <;> assumption)
end
