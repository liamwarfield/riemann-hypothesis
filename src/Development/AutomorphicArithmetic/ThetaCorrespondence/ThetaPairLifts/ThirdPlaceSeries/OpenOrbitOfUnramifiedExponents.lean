module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSizesOfStdKer
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BkLawEntries
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntriesCombinedReal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombined
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsVariant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointEvaluationSideStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsThird
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRow_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hSWU hL N S Γ
  have hE := _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA
    (GlobalTheory.T.diagonalRow_of_siegelWeil_unitary hSWU) hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun _ q => ⟨q.x.rx⟩)
  have hr := RowE.row hE
  exact ⟨_root_.GlobalTheory.Fc.RL.LinkedAt.of_row hr,
    _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (hr.imp fun _ _ _ h => GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll h)⟩
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  first | exact @_root_.GlobalTheory.miStarRow_alt_alt | exact _root_.GlobalTheory.miStarRow_alt_alt | (intros; apply _root_.GlobalTheory.miStarRow_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLabOfLayer
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GenPin
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.Fc.LabLinked
def GenPinAlt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : Prop :=
  ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)
section Rows
end Rows
end GlobalTheory.Fc.LabLinked
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.Fc.LabLinked
set_option maxHeartbeats 2000000 in
theorem typeLab_of_gen_alt_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep) : GlobalTheory.LabPin.TypeLab D rep := by
  have e : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      ∀ rep' : D'.what₂.FT → Formalism.L2.NG.FinTyp D'.host.E D'.R.r, HEq a.nt.rep rep' → GlobalTheory.LabPin.TypeLab D' rep' := by
    rintro _ rfl hl' rep' hr
    obtain rfl := eq_of_heq hr
    refine _root_.UpperTheory.Lit.Dz.localBesselMultiplicityOne hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.A.lab a.nt.row a.depth hl' ?_
    intro k v
    refine ⟨a.nt.A.grp.kv k v, ?_⟩
    rw [← hp k]
    exact a.nt.A.grp.tg_tame k v
  exact e D a.nt.eq hl rep hrep
section Rows
open _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem ties_of_nAtData_real (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} {R : RealDat3 D A3 Ks} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y) {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u}
    (s : SAt R.toRealDat F.lv2 Y.eE F0)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (hg : GoodFTAll D) : Ties D := by
  have hR := GlobalTheory.Mem.R3.RowFrameParts.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y
  have hT := _root_.GlobalTheory.Fc.LabLinked.typeLab_of_gen_alt_alt hG hZ a hl hp _ r.rep_eq
  exact ⟨s.P.X, s.P.G, s.S.hI.eHH,
    GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.eE F0 s Y.PY Y.hF
      (fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) hR.1 hR.2 hT hg⟩
end Rows
set_option maxHeartbeats 1000000 in
theorem ties_of_genPin_goodFTAll' (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a)
    (hg : GoodFTAll (q.w.D q.Z)) : Ties (q.w.D q.Z) :=
  _root_.GlobalTheory.Fc.LabLinked.ties_of_nAtData_real hG hZ (D := (q.w.st q.Z).toD7) q.core_data_of_point.row q.saturationAtWeightedPoint (lab_of_rows q.x.what₂) hp hg
theorem ties_of_built_genPin (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a) {Q : V4.Slot} {κ : Par}
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : GoodFTAll D → Ties D := by
  refine Built.ind (R := fun D _ _ _ => GoodFTAll D → Ties D) ?_ hb
  rintro K β c b - - ⟨q, b', -, e⟩
  have e1 : β.D = q.w.D q.Z := congrArg Sigma.fst e
  show GoodFTAll β.D → Ties β.D
  rw [e1]
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_genPin_goodFTAll' hG hZ q (hp K q)
theorem row_lab_of_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  intro hG hZ hL N S Γ hN ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA eps Fm hc x hx i => ?_⟩
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_built_genPin hG hZ (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun K q => hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2) (t x hx i).1 (hA Fm hc x hx i)
theorem row_lab_of_layer_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition :=
  fun hG hZ hL N S Γ hN =>
    _root_.GlobalTheory.Fc.LabLinked.row_lab_of_good_alt_alt hG hZ hL N S Γ fun K B f T w Z Wt p0 t nch n xd c m =>
      (hN K B f T w Z Wt p0 t nch n xd c m).elim fun e => e.1.zeta
end GlobalTheory.Fc.LabLinked
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_ft_entries_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  first | exact @_root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | exact _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | (intros; apply _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealGroupInputsCombined
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.RL
set_option maxHeartbeats 2000000 in
theorem at_row_hLamP_alt_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition := by
  intro h1 h2 h3 h4 a1 a2 a5 a6 a7 a12 a13 hG hL N S Γ
  refine _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (EvP.mono (fun κ K _ H β _ c b hl => ?_) LamLinked.evP_params))
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have e1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => Nonempty (ParameterChoice' s.1 s.2.1.L)) he
  have e2 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition s.1 s.2.1 c s.2.2) he
  refine cast e2.symm ?_
  have hIR := _root_.GlobalTheory.Fc.RL.LamLinked.isotRank_of_wit_alt h1 h2 h3 h4 a1 a2 a5 a6 a7 a12 a13 hG q w.y.y.host ⟨_, cast e1 (H β)⟩
  show Formalism.L2.Rows.RowsHoldLam3 b'.P
  rw [show b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x from congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).1
    (GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems h1 h2 h3 h4 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG q.O.ex.p0 w.x.Y w.x.Z w.x.pins w.y.intersectionNumber_baseChange w.y.y.host hIR)
end GlobalTheory.Fc.RL

theorem _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition :=
  _root_.GlobalTheory.Fc.RL.at_row_hLamP_alt_alt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HarishChandraInputsCombined
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fc.KapLinked
section Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Rows
set_option maxHeartbeats 2000000 in
theorem row_kap_of_row_lam_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a15 a16 a17 hL N S Γ h
  obtain ⟨R, hR, h⟩ := h
  refine ⟨R, hR, Row.imp h fun 𝒜 σ s hl => ?_⟩
  have key : AtAll (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) 𝒜 σ := by
    intro eps Fm hc x hx i
    obtain ⟨κ, -, -, hb⟩ := s Fm hc
    refine Built.ind (Bd := _root_.GlobalTheory.Fc.BundleCondition) (R := fun D _ _ b => (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → Formalism.L2.Rows.RowsHoldLam3 b.P →
      Formalism.L2.Rows.RowsHoldKap3 b.P) ?_ (hb x hx i).1 ⟨_, ⟨Fm.params x hx i⟩⟩ (hl Fm hc x hx i)
    intro K β c b _ _ hk
    obtain ⟨q, b', ⟨w⟩, he⟩ := hk
    have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (∃ L : SizeData₂ s.1, Nonempty (ParameterChoice' s.1 L)) →
      Formalism.L2.Rows.RowsHoldLam3 s.2.2.P → Formalism.L2.Rows.RowsHoldKap3 s.2.2.P) he
    refine cast e.symm fun hP hLam => ?_
    have hb' : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
    change Formalism.L2.Rows.RowsHoldLam3 b'.P at hLam
    change Formalism.L2.Rows.RowsHoldKap3 b'.P
    rw [hb'] at hLam ⊢
    have hM : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat :=
      _root_.GlobalTheory.T.twisted_multiplicity_one a6 a7 a2 a1 a8 a9 a10 a15 a16 a17 q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
        q.x.what₂.r.z.pins.char q.x.what₂.exAt w.y.y.host hP q.B.ccK_top q.x.what₂.r.z.pins.keep.guard (goodTypes_of_rows q.x.what₂)
    exact GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace ⟨a3, a4, a5, a1, a2⟩ _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG _ w.x.Y w.x.Z _ w.x.pins w.y.intersectionNumber_baseChange hLam
      (isot_ne_bot_of_rows a1 a17 q.x.what₂ hM) q.x.obj.kapR
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.KapLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  first | exact @_root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | exact _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | (intros; apply _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtHDivGOfMi
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtHDivGOfMi
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc.DivLinked
section Read
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
end Read
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_built_of_bWit {R : BdP _root_.GlobalTheory.Fc.BundleCondition} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : GlobalTheory.Fc.Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)
theorem linked_atAll_of_imp {A R : BdP _root_.GlobalTheory.Fc.BundleCondition}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → A _ _ c b → R _ _ c b)
    (hA : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll A)) : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.DivLinked.of_built_of_bWit (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)
section Wit
variable (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
  GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
  {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
include hC
theorem hDivG_of_mIstar2 (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hB : R3.Rw.BkLaw (q.w.D q.Z))
    (hM : (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) : _root_.GlobalTheory.Fc.R1.DivisorBundleCondition _ _ c b := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => (r.B.Q.Rl.toCx3 r.B.Q.F).MIstar2 (r.B.Q.F.eV (r.B.Q.Rl.toCx3 r.B.Q.F).zs) r.B.Q.sEE →
      GlobalTheory.Cp.DivRows3G r.P) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := fun hM =>
    divisionRows_pairing_vanishes_of_rational_pairing_law hC w.x w.y.intersectionNumber_baseChange hB
      (GlobalTheory.Div.pairing_definite_base_vanish_of_miStar2 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F 1 w.y.intersectionNumber_baseChange.ok w.y.intersectionNumber_baseChange.sep w.x.pins.char
        w.y.intersectionNumber_baseChange.prim w.x.sEE hM)
  rw [← w.y.eq] at h
  exact h hM
end Wit
theorem hDivG_linked_of_mIstar2 (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CasselmanWallach)
    (h4 : GlobalTheory.Published.HarishChandraFinite) (h5 : GlobalTheory.Published.CuspRapidDecay) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
    (hB : ∀ (K : Ctx) (q : WPt p.s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z))
    (hM : _root_.GlobalTheory.Fc.RL.LinkedAt p fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) =>
      (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDivisorCondition :=
  _root_.GlobalTheory.Fc.DivLinked.linked_atAll_of_imp (R := _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) (fun K q _ _ w h => _root_.GlobalTheory.Fc.DivLinked.hDivG_of_mIstar2 ⟨h1, h2, h3, h4, h5⟩ w (hB K q) h) hM
theorem at_hDivG_main_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition :=
  fun _ _ h3 h4 h5 h6 h7 _ _ _ _ hB hM => _root_.GlobalTheory.Fc.DivLinked.hDivG_linked_of_mIstar2 h5 h6 h7 h3 h4 _ hB hM
end GlobalTheory.Fc.DivLinked
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtHDivGOfMiStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bk_law_entries_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition :=
  _root_.GlobalTheory.Fc.DivLinked.at_hDivG_main_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinLinkedRealization
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinLinkedRealization
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.JoinLinked
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section IndefiniteRowSideFullHecke
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
theorem join_linked_realization_alt (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S0 : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (P : SPack D fun u => (Rc.T.cols.forms u).to0)
    (S : SRest P) (hS0 : S0 = S.toRealSpectralMatching Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S0) (c : ℝ) (hPins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) (hH : Holds x.R x.F)
    (hSee : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS)
    (hEv : EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G
      (iotaX P.X P.inst).toMulEquiv y.tS c)
    (hRow : RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j) :
    Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc S0 (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) := by
  subst hS0
  have hRR := (GlobalTheory.Mem.R3.rowLat_ties hR _ _ _ _ _ x.A3 _ x.R x.F x.cG _ x.Y x.Z x.pins hH).1
  exact (_root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt D L hT Gi Gl K Yd cX ex x Rc P S y c 1 (schurAll hR.2.2.2.1 hR.2.2.2.2 D) hPins hH hH.ok hH.sep hRR
    (rowConditions_at_companion_from_readings D L hT Gi Gl K Yd cX ex x).2.1 hSee hEv hRow).1
end IndefiniteRowSideFullHecke
section Wit
open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.SRe
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
set_option maxHeartbeats 2000000 in
theorem selJ_of_bWit (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c} (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (t : b.Comparison₂) : _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition _ _ c b := by
  show Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := b.R) (S := b.S) (Q := b.B.Q))
  have hPins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
    have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation r.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := t.pins
    rw [w.y.eq] at h
    exact h
  obtain ⟨sP, sS, hP, hS, hSeq⟩ := w.s
  have hx : w.a.x = w.x := eq_of_heq w.ax
  have hM := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w.a _ q.saturationAtWeightedPoint
  rw [hx] at hM
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by
    rw [w.recPin.s.cols]
  have hN := move hF (fun _ P S t c => SeeAt w.x.R.toRealDat w.x.F.lv2 P.X P.inst t ∧
      EvalTieT (MP w.x.R.toRealDat) w.x.R.toRealDat.ν0 w.x.R.toRealDat.fd0 (EP w.x.R.toRealDat w.x.F.lv2) P.X P.G
        (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ w.x.R.toRealDat w.x.Y.eE P.X P.inst P.G t S.j)
    (P := sP) (S := sS) (t := w.y.y.tS) (c := w.y.y.cS) hP hS w.pt.1 w.pt.2 hM
  have hJ := _root_.GlobalTheory.Fc.JoinLinked.join_linked_realization_alt hR w.x b.R b.S sP sS hSeq w.y.y w.y.y.cS hPins w.y.intersectionNumber_baseChange hN.1 hN.2.1 hN.2.2
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := b.R) (S := b.S) (Q := r.B.Q))) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := hJ
  rw [← w.y.eq] at h
  exact h
end Wit
section Constructions₂
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_built_of_bWit {R : BdP _root_.GlobalTheory.Fc.BundleCondition} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : GlobalTheory.Fc.Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)
theorem linked_atAll_of_imp {A R : BdP _root_.GlobalTheory.Fc.BundleCondition}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → A _ _ c b → R _ _ c b)
    (hA : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll A)) : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.JoinLinked.of_built_of_bWit (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)
end Constructions₂
theorem at_selJ_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesCover →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition :=
  fun _ _ h1 h2 h3 h4 h5 _ _ _ _ _ _ hT =>
    _root_.GlobalTheory.Fc.JoinLinked.linked_atAll_of_imp (A := _root_.GlobalTheory.Fc.HasCompatibility) (R := _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition) (fun _ _ _ _ w ht => _root_.GlobalTheory.Fc.JoinLinked.selJ_of_bWit ⟨h1, h2, h3, h4, h5⟩ w (Classical.choice ht)) hT
end GlobalTheory.Fc.JoinLinked
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinLinkedRealizationStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entries_combined_real_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition := by
  first | exact @_root_.GlobalTheory.Fc.JoinLinked.at_selJ_alt | exact _root_.GlobalTheory.Fc.JoinLinked.at_selJ_alt | (intros; apply _root_.GlobalTheory.Fc.JoinLinked.at_selJ_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtTie
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasTie
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPinTwArgs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPinTwArgs
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open scoped TensorProduct in
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.IndefR.principalLevelFrame in
theorem rowLocPin_congr_alt {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    {θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {PY PY' : principalLevelFrame.RowPsi V D.R.r}
    {M M' : Formalism.IndefR.Mult.DSModel V Sp} {J J' : Bool → Set (GA D V)} {χ χ' : Bool → GA D V → ℂ}
    {e e' : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {eFT : D.what₂.FT ≃ principalLevelFrame.FTR θ PY M J χ e}
    {eFT' : D.what₂.FT ≃ principalLevelFrame.FTR θ' PY' M' J' χ' e'} (hθ : θ = θ') (hP : PY = PY') (hM : M = M') (hJ : J = J')
    (hχ : χ = χ') (he : e = e') (hE : HEq eFT eFT') (h : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp θ PY M J χ e eFT) :
    _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp θ' PY' M' J' χ' e' eFT' := by
  subst hθ hP hM hJ hχ he
  cases hE
  exact h
set_option maxHeartbeats 4000000 in
theorem rowLocPin_twArgs_alt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (lp : Formalism.L2.LPTiedPlaceholder (w.st Z).toD7)
    (hr : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp t.r.z.R.θ t.r.Y.PY (t.r.z.R.MY 0)
      (fun s => levS _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun _ => t.r.z.R.e0) t.r.Y.eFT) :
    _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp a.x.R.θ a.x.Y.PY (a.x.R.MY 0)
      (fun s => levS _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun _ => a.x.R.e0) a.x.Y.eFT := by
  have hPY := a.PY
  have hE := a.eFT
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hPY hE ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, Y, _⟩ := x
  dsimp only at pack hPY hE ⊢
  cases pack
  exact _root_.GlobalTheory.Mem.Top.Bl.rowLocPin_congr_alt lp rfl (eq_of_heq hPY).symm rfl rfl rfl rfl hE.symm hr
set_option maxHeartbeats 4000000 in
theorem locPin_level_character_of_bWit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0) (fun s => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun s => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun _ => w.x.R.e0) w.x.Y.eFT := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro κ K _ q c b w _
  rw [show b.R.T.n.gal = q.core_data_of_point.a.all.gal from w.recPin.s.gal, ← eq_of_heq w.ax]
  exact _root_.GlobalTheory.Mem.Top.Bl.rowLocPin_twArgs_alt w.a _ q.core_data_of_point.row.rowLoc
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPinTwArgsStatement
alias GlobalTheory.T.local_level_character_pin_of_witness :=
  GlobalTheory.Mem.Top.Bl.locPin_level_character_of_bWit
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitCfEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitCfEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 4000000 in
theorem bwit_cf_eq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.x.R.C = b.R.T.n.cf := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ q c b w _ => ?_
  have hR : b.R.T.n.cf = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst w.recPin.s.chr
  rw [hR]
  have hC : q.x.what₂.r.z.R.toRealDat.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  rw [← hC]
  obtain ⟨x, a, ax, y⟩ := w
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  rfl
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitCfEqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq :
    ∀ (hL : UpperTheory.Zero.LLC.RecTExists) (p : GlobalTheory.Mem.Top.Bl.Parameters hL),
      GlobalTheory.Fc.EvP fun _ K =>
        ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c)
          (w : GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.x.R.C = b.R.T.n.cf :=
  GlobalTheory.Mem.Top.Bl.bwit_cf_eq_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PgEqOfLinked
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PgEqOfLinked
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Div.PgTie
open Classical in
set_option maxHeartbeats 4000000 in
theorem pgEq_of_linked_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all ?_
  intro _ K _ q c b w _
  have hk := w.recPin.k.std
  rw [image_congr hk.X_eq hk.seam hk.Pr]
  have hl := q.x.what₂.r.z.lev.Pg
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hl.trans (image_refl _ rfl _).symm
end GlobalTheory.Div.PgTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PgEqOfLinkedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) :=
  _root_.GlobalTheory.Div.PgTie.pgEq_of_linked_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSFinConjMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSFinConjMatch
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.LinkLev
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr
end GlobalTheory.Mem.R3.LinkLev
namespace GlobalTheory.Mem.R3.LinkLev
set_option maxHeartbeats 4000000 in
theorem tS_fin_conj_match_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ => ?_
  intro q c b w hsc
  obtain ⟨sP, sS, hP, hS, hb⟩ := w.s
  have see := q.saturationAtWeightedPoint.see
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hι := (GlobalTheory.Mem.JIota.heq_iota_iff _ _ w.y.y.instEq w.y.y.ιS).1 w.y.y.ιS_eq
  have hX : b.S.X = q.saturationAtWeightedPoint.P.X := by
    rw [hb]
    exact spack_X_eq_of_heq (by rw [w.recPin.s.cols]; exact rfl) sP q.saturationAtWeightedPoint.P hP
  have key := levels_of_twArgs w.a w.x w.ax q.saturationAtWeightedPoint.P.X q.saturationAtWeightedPoint.P.inst q.saturationAtWeightedPoint.t ⟨see.conj, see.mat⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact see.fin
  · exact conjLevel_of_setting_eq _ _ hX _ _ _ hι _ _ ht _ _ key.1
  · exact of_setting_eq (fun X h t => Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 X h t) _ _ hX _ _ _ _ ht key.2
end GlobalTheory.Mem.R3.LinkLev
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSFinConjMatchStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_level_conjugate_character_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  exact _root_.GlobalTheory.Mem.R3.LinkLev.tS_fin_conj_match_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleWitnessZeroSectionEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleWitnessZeroSectionEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro _ K _ q c b w hsc
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleWitnessZeroSectionEqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  exact GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerLast
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerLast
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.RecPinsTie
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), ∀ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (∀ hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → _root_.Formalism.IndefR.IndefiniteRealisationCompatible hp (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y r
  refine ⟨fun hp h => ⟨?_, ?_⟩, fun h => ?_, ?_⟩
  · exact x.Y.stdPsi
  · exact h
  · exact h
  · exact x.pins.keep.psi
end GlobalTheory.Mem.R3.RecPinsTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerLastStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_local_row_condition_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), ∀ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (∀ hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → _root_.Formalism.IndefR.IndefiniteRealisationCompatible hp (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  first | exact @_root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt | exact _root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt | (intros; apply _root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.TieOfLink
theorem tie_of_rpk_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) {x : TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y)
    (e : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) (hp : ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) :
    Nonempty b.Comparison₂ := by
  let hasPins (z : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) : Prop :=
    ∃ Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion z.B.Q,
      PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree z.B.Q ∧
      ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation z.B.Q,
        _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
  have hInput : hasPins (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) :=
    ⟨_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r, hpsi, h3, hp⟩
  have hBundle : hasPins (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := e.symm ▸ hInput
  obtain ⟨Rr, h⟩ := hBundle
  exact ⟨⟨Rr, h⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem nonempty_tie_of_wit (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y))
    (hloc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := _root_.GlobalTheory.T.recursion_local_row_condition_alt _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact _root_.GlobalTheory.Fc.TieOfLink.tie_of_rpk_alt b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩
theorem hasTie_of_linked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ => _root_.GlobalTheory.Fc.HasCompatibility := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((_root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq hL p).and (_root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq hL p)).and (_root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq hL p)).and (_root_.GlobalTheory.T.theta_level_conjugate_character_alt hL p)).and (_root_.GlobalTheory.T.local_level_character_pin_of_witness hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : _root_.GlobalTheory.Fc.HasCompatibility _ _ c b' := _root_.GlobalTheory.Fc.TieOfLink.nonempty_tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → _root_.GlobalTheory.Fc.HasCompatibility s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e
end GlobalTheory.Fc.TieOfLink
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtTie
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL
theorem at_tie_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt := by
  intro _ _ _ _ _ _ _ hL N S Γ _
  exact _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (_root_.GlobalTheory.Fc.TieOfLink.hasTie_of_linked _ _))
end GlobalTheory.Fc.RL
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtTieStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_tie_of_nonempty_extensionWithLaw : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt := by
  first | exact @_root_.GlobalTheory.Fc.RL.at_tie_alt | exact _root_.GlobalTheory.Fc.RL.at_tie_alt | (intros; apply _root_.GlobalTheory.Fc.RL.at_tie_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWb
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWb
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.PrimAt
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_wit_alt {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c} (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition _ _ c b := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem herm_wCell_last_mul_mulVec_eq_of_inWb (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) : _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  refine RowE.row (R := _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition) (RowE.of_all fun κ K β c b _ _ hl => ?_)
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition s.1 s.2.1 c s.2.2) he
  exact cast this.symm (_root_.GlobalTheory.Fc.RL.PrimAt.of_wit_alt w)
theorem linkedAt_hPA : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition :=
  fun _ N S Γ => _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (_root_.GlobalTheory.Fc.RL.PrimAt.herm_wCell_last_mul_mulVec_eq_of_inWb (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _)
end GlobalTheory.Fc.RL.PrimAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWbStatement
open GlobalTheory.Mem.Top.Bl

theorem GlobalTheory.T.linkedAt_hPA_prmR :
    ∀ (hL : UpperTheory.Zero.LLC.RecTExists) (N : NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
      GlobalTheory.Fc.RL.LinkedAt (parametersOfExtension N S Γ)
        GlobalTheory.Fc.R1.SlotPrimitivityCondition :=
  GlobalTheory.Fc.RL.PrimAt.linkedAt_hPA
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinked
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinked
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL
theorem rowE_dcPt_linked_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ => _root_.GlobalTheory.Fc.R1.DecompositionPointBundle) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hBundle := congrArg
    (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c =>
      _root_.GlobalTheory.Fc.R1.DecompositionPointBundle s.1 s.2.1 c s.2.2) he
  refine cast hBundle.symm ?_
  change GlobalTheory.Cp.DcPtG b'.P
  have hP : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
  rw [hP]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem linkedAt_hDcPtG : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition := by
  intro hL N S Γ
  exact _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (_root_.GlobalTheory.Fc.RL.rowE_dcPt_linked_alt _ _))
end GlobalTheory.Fc.RL
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinkedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition := by
  first | exact @_root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG | exact _root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG | (intros; apply _root_.GlobalTheory.Fc.RL.linkedAt_hDcPtG <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.S0.Open0ProofU
theorem open_orbit_of_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := _root_.GlobalTheory.T.linkedAt_hPA_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := _root_.GlobalTheory.T.linkedAt_tie_of_nonempty_extensionWithLaw P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := _root_.GlobalTheory.T.entries_combined_real_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := _root_.GlobalTheory.T.bk_law_entries_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := _root_.GlobalTheory.T.good_ft_entries_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie P.rayClassFieldSt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := _root_.GlobalTheory.T.weil_unitary_entries' P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩
end GlobalTheory.Fc.S0.Open0ProofU

theorem _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) :=
  _root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt
end
