module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Rethread
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.ResCore
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TripleWeilTransfer
variable {D : D7}
theorem triple_exists_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro _ _ _ _ D ψ θ hψ hθ W W₁ X A A₁ B α β _ ⟨ωA₀, ωB₀, Pi, rf, rl, p, p', hm⟩ ωA ωB hA hB
  refine ⟨Pi, rf, rl, p, p', hA, hB, hm.irred, ?_, ?_⟩
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta true hm.weilA hA q Φ (isThetaFunO_of_mem_algF hψ hθ true A B hΦ))
      hm.mapA
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta false hm.weilB hB q Φ (isThetaFunO_of_mem_algF hψ hθ false A₁ B hΦ))
      hm.mapB
end GlobalTheory.TripleWeilTransfer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_weil_transfer_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  first | exact @_root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching | exact _root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching | (intros; apply _root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRatioMemNumberField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
namespace GlobalTheory.RowEx.RatioField
open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
end GlobalTheory.RowEx.RatioField
namespace GlobalTheory.RowEx.RatioField
open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
theorem twistRatio_mem_numberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → NFRatio := by
  intro _ hTR hFD _
  obtain ⟨CF0, hF⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hsc => ?_⟩
  have hRec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hS.size, hS.host⟩
  haveI : Finite T := hS.fin
  have key : ∀ (sc : Consts) (G : GridData R.toLevCh sc), sc = ⟨1, CF, large₂.sc.b⟩ →
      InNF fun _ σ => ∀ i j, LRatiosIn G σ A.μ0 i j := by
    rintro sc G rfl
    obtain ⟨hcm, -, hfd, hbc, -⟩ := hF C0 le_rfl D large₂ he hx hRec T R.toLevCh A.μ0 hS.core.lev G
    exact inNF_ratios hTR hS.core.lev G hcm hfd hbc
  exact key ch.sc ch.G hsc
end GlobalTheory.RowEx.RatioField
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftInjNonVanTypeNZOfPrints
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EulerFactorFromDoubling
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KplugFill
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.Exh.Top
theorem downNe_k_of_hypotheses' : ResidueKilled.DM → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D :=
  fun hDM hSP => downNe_of_core hDM PositivityTheory.Rg.Rsw.resCore hSP
end GlobalTheory.Core.Rk.Exh.Top
end
end
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downNe_of_eulerRight_doubling : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  first | exact @_root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' | exact _root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' | (intros; apply _root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory.Core.Rk.LiftOnto
theorem liftInj_nonVan_typeNZ_of_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL →
    GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram →
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
      [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  intro hDec hDbl hGL hHecke hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull
  have hEul : GlobalTheory.Core.Rk.IP.EulerRight D := GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified hDec hGL D
  have hPole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole := GlobalTheory.LiftPoleObj.simplePole_of_hecke hHecke
  have hNe : DownNe D := _root_.GlobalTheory.T.downNe_of_eulerRight_doubling hDbl hPole D hEul
  have hNV : ∀ i t, NonVan R i t := GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown D hNe G Pl0 T A Ks R F hG hFull
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.T.thetaLift_generation_finitePlaces hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.T.thetaLift_generation_at_realPlaces D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.T.downwardThetaLift_preserves_good D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.T.goodTypes_exclude_levelCharacter D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes hDec hHowe D G Pl0 T A Ks R F hG hFull
  have hOk : ∀ i t (ok : Pl D.host.E → Prop), UnrCorr R i t ok := by
    intro i t ok h hh s c y hy h1 h2 B B' hB hB' w hw _
    exact hU i t h hh s c y hy h1 h2 B B' hB hB' w hw trivial
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  exact ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hOk i A.μ0 _, hOk i A.μ0 _, hPar i A.μ0⟩),
    fun i t => ⟨hNV i t, hTNZ i t⟩⟩
end GlobalTheory.Core.Rk.LiftOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  first | exact @_root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | exact _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConditionOfMemberHypotheses
section
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx _root_.Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
structure MemberHypotheses : Prop where
  m1 : GlobalTheory.Published.HarishChandraAnalyticity
  m2 : GlobalTheory.Published.DiscreteSeriesClassification
  m3 : GlobalTheory.Published.CuspRapidDecay
  m4 : GlobalTheory.Published.HarishChandraFinite
  m5 : GlobalTheory.Published.CuspTraceClass
  m6 : GlobalTheory.Published.DixmierMalliavinFactorisation
  m7 : GlobalTheory.Published.FlathFactorisation
  m12 : GlobalTheory.Published.ZelevinskyPolynomialRing
  m13 : GlobalTheory.Published.GeometricLemma
  m14 : GlobalTheory.Published.GreenCuspidal
theorem condition_of_memberHypotheses (c : GlobalTheory.Published.DiscreteSeriesCover) (h1 : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems)
    (h3 : GlobalTheory.Published.HeckeLPartialContinuation) (m : MultL) (r : RowRatW) : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  ⟨c, h1, h3, m,
    (StepW.and ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans m) r).trans
      (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v => ⟨G.1 Z hX Wt z a b c d, G.2 Z hX Wt z a b k c d e g u v⟩)⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraActionByLineDerivatives
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumPureLineDifferentiable
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLinePureW
theorem hasDerivAt_thetaSum_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' h γ hγ f _ f₁ hD φ hφ hv u
  have H := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP G.M B.ψ X.β (X.β / X.α) om h.base.cm h.base.std h.geo.hM h.weil γ hγ 1 (fun _ => f) (fun _ => f₁)
    (fun _ => φ) (fun _ => ⟨hφ, hv⟩) (fun _ => hD) u
  simpa using H
end GlobalTheory.ThetaLinePureW
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_pure_line_differentiable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | exact _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | (intros; apply _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.MaxLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.RealLift Formalism.BasicNotions.TH
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_derivation_action_weil (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := _root_.GlobalTheory.T.real_lift_lie_second_order hPr hD hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hPr hD hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  intro γ hγ f hf
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
  exact ⟨_, mem _, h2⟩
theorem thetaSum_weil_hasDerivAt (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) (f : SInf F (Fin a × Fin (a + a')))
    (hf : f ∈ G.M.Pol B.ψ B.emb) (f₁ : SInf F (Fin a × Fin (a + a')))
    (hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) :
    HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (pure f φ))))
      (thetaSum F (G.M.co.rho B.ψ u (pure f₁ φ))) 0 :=
  _root_.GlobalTheory.T.thetaSum_pure_line_differentiable hPr F E σ B a a' G X om om' h γ hγ f hf f₁ hA φ hSB hev u
theorem exists_line_derivative_maxLie (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Ψ ∈ algD G.M B.ψ B.emb,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Ψ x) 0) ∧
      ∀ u, HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) Φ)))
        (thetaSum F (G.M.co.rho B.ψ u Ψ)) 0 := by
  have hψ : IsStd B.ψ := h.base.std
  have hM := h.geo.hM
  have hsch : ∀ p, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting h.weil).pres p Φ hΦ
  have hAD := GlobalTheory.SquareAgree.HeisDeriv.algD_le_schA G.M B.ψ B.emb hM
  have hrs : ∀ u, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.co.rho B.ψ u Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ u Φ hΦ
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_, fun u => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simp only [map_zero, GlobalTheory.SquareAgree.CoinvPass.rho_zero']
      simpa [thetaSum] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a₁ b₁ ha₁ hb₁ ha hb =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    obtain ⟨b₂, hb₂, hpb, htb⟩ := hb
    refine ⟨a₂ + b₂, add_mem ha₂ hb₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_add (f := _), Pi.add_apply]
      exact (hpa x).add (hpb x)
    · have e : (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (a₁ + b₁)))) =
          fun t => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) a₁)) +
            thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) b₁)) := by
        funext t
        rw [map_add (f := _), GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hsch _ _ (hAD ha₁)))
          (hrs u _ (hsch _ _ (hAD hb₁)))]
      rw [e, GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hAD ha₂)) (hrs u _ (hAD hb₂))]
      exact (hta u).add (htb u)
  | smul c a₁ ha₁ ha =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    refine ⟨c • a₂, Submodule.smul_mem _ c ha₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hpa x).const_mul c
    · simp only [map_smul, GlobalTheory.SquareAgree.CoinvPass.rho_smul', GlobalTheory.SquareAgree.HeisDeriv.thetaSum_smul]
      exact (hta u).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    obtain ⟨f₁, hf₁, hA⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_derivation_action_weil hPr h γ hγ f hf
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, φ, hf₁, hSB, hev, rfl⟩, fun x => ?_, fun u => ?_⟩
    · exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
    · exact _root_.GlobalTheory.SquareAgree.MaxLie.thetaSum_weil_hasDerivAt hPr h γ hγ f hf f₁ hA φ hSB hev u
end Gen
theorem maximal_lie_subalgebra_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _hTr hO hT Pi rf rl p p' _hm N hN τ Y hY
    ΦD hΦD Φ hD
  have hψB := hO.psi
  subst hψB
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨Ψ, hΨ, hpt, hth⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_line_derivative_maxLie hPr hT γ hγ ΦD (hN.1 hΦD)
  have hΨN : Ψ ∈ N := hN.2.2.2 γ hγ ΦD hΦD Ψ hΨ hpt
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algA' Ψ hΨ
  refine ⟨Ψ, hΨN, Φ₁, hΦ₁, hD₁, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := cA.surjective z
  have key : (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) =
      fun t => thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (1, γ (Multiplicative.ofAdd t)) ΦD)) := by
    funext t
    have k := (hO.weilA ΦD Φ hD 1 (oneP θ X τ Y t)).2 u
    rw [GlobalTheory.LocWeilAct.conjU_one', ← hγt t] at k
    exact k.symm
  show HasDerivAt (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) (Φ₁ (cA u)) 0
  rw [key, ← hD₁.2 u]
  exact hth u
end GlobalTheory.SquareAgree.MaxLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_lie_algebra_action_by_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  first | exact @_root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | exact _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | (intros; apply _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts <;> assumption)
end
end
