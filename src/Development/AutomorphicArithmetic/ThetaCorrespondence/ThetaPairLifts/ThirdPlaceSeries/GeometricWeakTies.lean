module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
public import Development.AutomorphicArithmetic.ResidueCharacters.ClosedOfAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc.S0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx _root_.Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
variable (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition)
def CovolumeBoundThirdPlaceSeries : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH))
def FunctionalCondition : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun Fm => DIVinN Fm) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH))
def GeometricWeakCompatibility' : Prop := Row Q Lk (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∃ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.BigOn.More (b.part t).pt)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
structure OpenParameterStatements (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Prop where
  hPA : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition
  hLamP : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition
  hDivG : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDivisorCondition
  hDcPtG : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition
  selJ : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition
  tie : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.Row_tie_alt
  lab : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowLabelCondition
  good : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowGoodnessCondition
  geo : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility'
  mi : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition
  kap : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowKappaCondition
  df : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowDefectCondition
end GlobalTheory.Fc.S0
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelP
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXLevChi
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXLevChi
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepLevelP
theorem ioX_levChi_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)), F.1 ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) g :=
  fun W hW t F hF κ hκ φ x g => ioX_levChi_gen (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) hW.bot.hyp.2.2.2.1.lev hW.bot.hyp.2.2.2.1.models
    hW.bot.hyp.2.2.2.1.chain t F hF κ hκ φ x g
end GlobalTheory.StepLevelP
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXLevChiStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_projection_level_character_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)), F.1 ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) g := by
  first | exact @_root_.GlobalTheory.StepLevelP.ioX_levChi_alt | exact _root_.GlobalTheory.StepLevelP.ioX_levChi_alt | (intros; apply _root_.GlobalTheory.StepLevelP.ioX_levChi_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelP
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopStep
open GlobalTheory.Fam.Inhab GlobalTheory.Fam.FamInhab
section
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)
end
theorem ioXT_levelP_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (g : GlobalTheory.Fam.Geo D) t j (h : j + 2 * 0 + 2 = D.R.m) (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t), ∃ h' : F.1 ∈ LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e), (GlobalTheory.Published.CuspRapidDecay → (ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h ⟨F.1, h'⟩).1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ Q x, liftS (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) ((_root_.GlobalTheory.Fam.pk_z W).νX t) ((_root_.GlobalTheory.Fam.pk_z W).fdX t) (F.1 x) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) • (ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h ⟨F.1, h'⟩).1 ((commOf (_root_.GlobalTheory.Fam.pk_z W) u g).ItT j h Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP g t j h F
  have hC := hP.bot.hyp.2.2.2.1
  have h1 := cxp_le (_root_.GlobalTheory.Fam.complexLevelStructure W) hP.hTop t F.2
  exact ⟨h1, fun hc => top_mem (_root_.GlobalTheory.Fam.complexLevelStructure W) hc hC.lev hC.models hC.chain t j h ⟨F.1, h1⟩ F.2,
    fun v hv Q x => lift_ioX_pt (_root_.GlobalTheory.Fam.complexLevelStructure W) hC.lev hC.models hC.chain t j h ⟨F.1, h1⟩ (_root_.GlobalTheory.T.extra_projection_level_character_alt W hP t ⟨F.1, h1⟩ F.2) hv Q x⟩
end GlobalTheory.TopStep
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelPStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_column_range_membership_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (g : GlobalTheory.Fam.Geo D) t j (h : j + 2 * 0 + 2 = D.R.m) (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t), ∃ h' : F.1 ∈ LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e), (GlobalTheory.Published.CuspRapidDecay → (ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h ⟨F.1, h'⟩).1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ Q x, liftS (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) ((_root_.GlobalTheory.Fam.pk_z W).νX t) ((_root_.GlobalTheory.Fam.pk_z W).fdX t) (F.1 x) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) • (ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h ⟨F.1, h'⟩).1 ((commOf (_root_.GlobalTheory.Fam.pk_z W) u g).ItT j h Q x) := by
  first | exact @_root_.GlobalTheory.TopStep.ioXT_levelP_alt | exact _root_.GlobalTheory.TopStep.ioXT_levelP_alt | (intros; apply _root_.GlobalTheory.TopStep.ioXT_levelP_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPoints
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLowerAtPoints
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLowerAtPoints
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.LevLow
theorem levelPrime_lower_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  intro hL p
  have hA : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
    RowE.of_all fun _ K β _ b _ _ _ =>
      admissibleRanks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_mass K β.X β.c.isOver β.c.dsig_eq)
  exact (EvP.and (RowE.and hA (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)) eventually_le_trace).mono
    fun _ _ _ H β hq c b hl => H.2 β (H.1 β hq c b hl).1 (H.1 β hq c b hl).2
end GlobalTheory.Core.LevLow
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLowerAtPointsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lower_bound_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  first | exact @_root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt | exact _root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt | (intros; apply _root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLeAtPoints
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLeAtPoints
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
theorem levelPrime_le_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  intro hL p
  exact eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β
end GlobalTheory.LevelPrimeUpper
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLeAtPointsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_upper_bound_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  first | exact @_root_.GlobalTheory.LevelPrimeUpper.levelPrime_le_at_points_alt | exact _root_.GlobalTheory.LevelPrimeUpper.levelPrime_le_at_points_alt | (intros; apply _root_.GlobalTheory.LevelPrimeUpper.levelPrime_le_at_points_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPoints
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.HypAt
theorem hypL_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  intro hL p A B
  exact (EvP.and (RowE.and (_root_.GlobalTheory.T.trace_lower_bound_all_members' hL p) (_root_.GlobalTheory.T.trace_upper_bound_all_members' hL p)) (evP_hypL A B)).mono fun _ _ _ H β hq c b hl =>
    H.2 β fun u => ⟨(H.1 β hq c b hl).1 u, (H.1 β hq c b hl).2 u⟩
end GlobalTheory.Core.HypAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPointsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degHypL_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  first | exact @_root_.GlobalTheory.Core.HypAt.hypL_at_points_alt | exact _root_.GlobalTheory.Core.HypAt.hypL_at_points_alt | (intros; apply _root_.GlobalTheory.Core.HypAt.hypL_at_points_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.At23OfAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowOn
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
def RowOnAlt (Q : D7 → ℕ → Prop) (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowOnAt (Fm.L x i) X.ρ (Q (Fm.D x i)) A B
def SecondBoundCondition (A B : ℝ) : Prop := _root_.UpperTheory.N.RowOnAlt (fun _ l => l = 2) A B
def ThirdBoundCondition (A B : ℝ) : Prop := _root_.UpperTheory.N.RowOnAlt (fun D l => l = 3 ∧ l ∉ D.host.small) A B
end UpperTheory.N
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowThree
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem rowThreeAt_of_setup_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    RowOnAt L X.ρ (fun l => l = 3 ∧ l ∉ D.host.small) 6000 30000 := by
  rintro i hTw ⟨h3, hs⟩ π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h2 : D.nd.l i ≠ 2 := by omega
  have hq : D.nd.l i ≠ D.host.q := h3 ▸ (three_ne_q D).1
  have hd : D.nd.l i ≠ D.host.d := h3 ▸ (three_ne_q D).2
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k => h3 ▸ three_ne_g D k
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hle : D.nd.l i ≤ D.host.splitBound := by have := S.split; omega
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small hl).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, D.host.cls_splitK_or_small hl hle hq hd,
    fun _ v hv => GlobalTheory.HubLoc.ramIdx_eq_one D.host hl hN v hv, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := D.host.split_small _ hl h2 hle
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (cycAt_of i fun e => absurd e h2) hL (decl_split D i h2 hj) (locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs0 : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hs
  have hsl : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
    unfold RowSmall.sl
    rw [hs0, Nat.factorization_eq_zero_of_not_dvd hN]; rfl
  have hh := h0_le D i dc.col (fun e => absurd e h2) hs0.ge (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P X.ρ S.kill S.sha i hTw hsl π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
end UpperTheory.N
theorem UpperTheory.N.exists_nonneg_threeC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.rowThreeAt_of_setup_alt hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowTwo
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.onAt_eq_two_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowOnAt L X.ρ (fun l => l = 2) 6000 30000 := by
  intro i hTw h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hs : D.nd.l i ∈ D.host.small := by rw [show D.nd.l i = 2 from h2]; exact UpperTheory.Small.two_mem D.host
  have h4 : 2 ^ 2 ∣ D.host.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun _ => (h4.mul_right _).mul_right _) hL (UpperTheory.N.Two.decl_split D i h2)
    (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs2 : 2 ≤ D.nd.s0 i := by
    rw [D.nd.restNLevelExponent_of_two i h2]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization D.host.QS_pos.ne').1 h4
  have hh := UpperTheory.N.h0_le D i dc.col (fun _ => hs2) (by omega) (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_twoC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.onAt_eq_two_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyBoundAtTwoThreeOfLocalBounds
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem mid_of_rowOn_alt (Q : D7 → ℕ → Prop)
    (hQ : ∀ D l, l.Prime → Q D l → D.host.condN.factorization l = D.host.QS.factorization l)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : _root_.UpperTheory.N.RowOnAlt Q A B) {eps : ℝ} (Fm : FamP eps) :
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
      (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
      (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
      _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → ∀ k, TwistedPlaces.TwLoc (Fm.D x i) k → Q (Fm.D x i) ((Fm.D x i).nd.l k) →
        ∀ π ∈ (Fm.D x i).nd.Zgood k, Bd X.ρ k π (midF (Fm.L x i) C) := by
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1), ?_,
    fun x hxx hx i HW F Cm X C₂ hS k hTw hq π hπ => ?_⟩
  · have : 0 ≤ C0 := by linarith
    positivity
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hq π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : ((Fm.D x i).nd.l k).Prime := ((Fm.D x i).nd.lPrime k).out
  have hc : costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    Num.cost_le' (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hl (hQ _ _ hl hq) le_rfl
  unfold Bd at hb ⊢
  linarith
theorem boundAtTwoThree_of_local_bounds_at_two_three (h3qd : ∀ D : D7, 3 ≠ D.host.q ∧ 3 ≠ D.host.d)
    (h2 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B) (h3 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B)
    {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm := by
  obtain ⟨A, B, hA, hB, h2⟩ := h2
  obtain ⟨A', B', hA', hB', h3⟩ := h3
  obtain ⟨C, x0, hC, h2⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun _ l => l = 2) (fun D l _ (e : l = 2) =>
    Num.factorization_condN D (by rw [e]; exact UpperTheory.Small.two_mem D.host)) A B hA hB (fun Fm => h2 Fm) Fm
  obtain ⟨C', x1, hC', h3⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun D l => l = 3 ∧ l ∉ D.host.small) (fun D l _ (e : l = 3 ∧ l ∉ D.host.small) =>
    Num.factorization_condN' D (by rw [e.1]; exact (h3qd D).1) (by rw [e.1]; exact (h3qd D).2)) A' B' hA' hB' (fun Fm => h3 Fm) Fm
  refine ⟨max C C', max x0 x1, fun x hxx hx i HW F Cm X C₂ hS k hTw hl π hπ => ?_⟩
  have h0 : 0 ≤ max C C' := hC.trans (le_max_left _ _)
  rcases hl with hl | hl
  · have h := h2 x ((le_max_left _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_left C C') h0
    unfold Bd at h ⊢; linarith
  · have h := h3 x ((le_max_right _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_right C C') h0
    unfold Bd at h ⊢; linarith
end UpperTheory.N
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem at23_family_alt (hP : Hypotheses₂) {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm :=
  _root_.UpperTheory.N.boundAtTwoThree_of_local_bounds_at_two_three three_ne_q (_root_.UpperTheory.N.exists_nonneg_twoC_constants_of_prints hP) (_root_.UpperTheory.N.exists_nonneg_threeC_constants_of_prints hP) Fm
theorem boundAtTwoThree_n_linked (h : ∀ {eps : ℝ} (Fm : FamP eps), _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (GlobalTheory.Fc.Row.of_sel fun _ _ _ => closed_of_all _ fun Fm _ => h Fm)
theorem boundAtTwoThree_linked_of_recT (hP : Hypotheses₂) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.UpperTheory.N.boundAtTwoThree_n_linked (fun Fm => _root_.UpperTheory.N.at23_family_alt hP Fm) p
end UpperTheory.N
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormula
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormula
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem ker_mulVecLin_eq_U_of_formulaAt {p : PtAt ex Csz} (hp : p.PointConditions') (hD : 0 < (Df p).dQ p.P.A3.fam3.base3.μ0)
    (hPq : Function.Surjective ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec)
    {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieAt d a)
    (hI : ∀ u, (∀ i, psiK a.ch i u = 0) → u = 0) (hC : ∀ i j t, a.ch.c i j t ≠ 0)
    (hF : ∃ κ ze, FormulaAt a.ch κ ze) :
    LinearMap.ker (d.V p.P.A3.fam3.base3.μ0).mulVecLin = (Df p).U p.P.A3.fam3.base3.μ0 := by
  obtain ⟨κ, ze, hz, hf⟩ := hF
  have hc : cTot a.ch p.P.A3.fam3.base3.μ0 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hC i j _
  have hze : D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) ≠ 0 := by
    obtain ⟨n, hn, e⟩ := hz p.P.A3.fam3.base3.μ0
    refine (map_ne_zero _).2 fun z => ?_
    rw [z, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hinj := (_root_.GlobalTheory.T.iC_iota_mulVec_eq_iC p hp).1
  have key : ∀ y, p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = 0 ↔
      ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y = 0 := by
    intro y
    have e := _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq p hp p.P.A3.fam3.base3.μ0 y
    change p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = _ at e
    rw [e]
    constructor
    · intro h0
      have h1 := hinj (h0.trans (map_zero _).symm)
      funext i
      exact p.P.A3.fam3.base3.v0.embedding.injective (by simpa [cpt] using congrFun h1 i)
    · intro h0
      rw [h0]
      have : cpt p.P.A3.fam3.base3.v0.embedding (0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) → D.what₂.LL) = 0 := by
        funext i; simp [cpt]
      rw [this, map_zero]
      rfl
  have hκ : κ ≠ 0 := by
    obtain ⟨y, hy⟩ := hPq (Pi.single ⟨0, hD⟩ 1)
    have hne : p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) ≠ 0 := fun h0 => by
      have h2 := congrFun ((key y).1 h0) ⟨0, hD⟩
      rw [hy] at h2
      simp at h2
    obtain ⟨i, hi⟩ : ∃ i, psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (hI _ hall)
    exact FormulaAt.ne_zero ⟨hz, hf⟩ hc (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) hi
  ext y
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, DefSide.U]
  rw [← key y]
  constructor
  · intro h0
    apply hI
    intro i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hv : vK a.ch p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) i = 0 :=
      hs.symm.trans (by rw [h0]; exact map_zero _)
    have e2 := e.trans (by rw [hv, mul_zero])
    exact ((mul_eq_zero.1 e2).resolve_left (mul_ne_zero hze hc))
  · intro h0
    funext i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hz0 : psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) = 0 := by
      rw [h0]; exact psiK_zero _ _
    rw [hz0, mul_zero, ← hs] at e
    have h3 := (mul_eq_zero.1 e.symm).resolve_left hκ
    exact D.what₂.embLL.injective (by rw [h3]; exact (map_zero _).symm)
theorem leafKernel_of_linK_injK_constK_formula2K : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → LinK → InjK → ConstK → Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @Comparison₂ := by
  intro hB hS _ hI hC hF
  obtain ⟨CF0, hA⟩ := hS.atPt (hI.and (hC.and hF))
  refine ⟨CF0, fun CF hCF => (hA CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p hp b d hd => ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hd
  obtain ⟨q1, q2, q3⟩ := b d.G d.W d.n a ha.ok
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have h0 : 0 < (p.S false).D := hR ▸ R0.D_pos
  have v : d.O.vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  show LinearMap.ker (d.O.vmu _).mulVecLin = _
  rw [v]
  exact _root_.GlobalTheory.BigTop.Fun.ker_mulVecLin_eq_U_of_formulaAt hp h0 (wf.Pq_surj _) d a ha q1 (fun i j t => (q2 i j t).2) (q3 ha.ok.field)
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormulaStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafKernel_tie_of_claim_inputs : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | exact _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | (intros; apply _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRows
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRows
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1600000 in
theorem exists_unit_root_ze_leafC_of_square_nonzero (p : PtAt ex Csz) (hp : p.PointConditions') {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (ht : TieAt d a)
    (hwf : (Df p).WF) (hR : ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false)
    (hQ : (∀ b u, ConvK a.ch b u) ∧ (∀ u, (∀ b, psiK a.ch b u = 0) → u = 0) ∧
      (∀ i j t, SquareNonzero a.ch.W a.ch.S.B a.ch.rm t i j ∧ a.ch.c i j t ≠ 0) ∧
      (a.ch.FieldOK → ∃ κ ze, FormulaAt a.ch κ ze)) :
    ∃ ze : Tup p → D.what₂.LL, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
      LeafC (p.S false) (d.data ze ∅ fun _ => 0) := by
  classical
  obtain ⟨hL, hI, hC, hF⟩ := hQ
  obtain ⟨κ, ze, hz, hform⟩ := hF ht.ok.field
  obtain ⟨R0, hR0⟩ := hR
  obtain ⟨hinj, hrow⟩ := _root_.GlobalTheory.T.iC_iota_mulVec_eq_iC p hp
  have hzK : ∀ t, ze t ≠ 0 := fun t h => by
    obtain ⟨n, hn, e⟩ := hz t
    rw [h, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hze : ∀ t, D.what₂.embLL (ze t) ≠ 0 := fun t => (map_ne_zero _).2 (hzK t)
  have hc0 : ∀ t, cTot a.ch t ≠ 0 := fun t => (cTot_ne_zero_iff _ _).2 fun i j => (hC i j t).2
  have key : ∀ t (y : Fin ((Df p).nV t) → D.what₂.LL) (b : Fin d.n),
      D.what₂.embLL (ze t) * cTot a.ch t * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
        κ * D.what₂.embLL ((d.V t).mulVec y b) := by
    intro t y b
    rw [← _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq p hp t y, ht.sums t (TieModel.inUse p t) y b]
    exact hform t _ (_root_.GlobalTheory.T.eV0_mem_goodF' p hp t y) b
  have lin : ∀ (b : Fin d.n) (z : Fin (p.S false).D → D.what₂.LL),
      psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding z)) =
        ∑ k, D.what₂.embLL (z k) *
          psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1)) := by
    intro b z
    have := out_sum_tw (twAt D.what₂.embLL p.P.A3.A.v0) (psiL a.ch b (hL b))
      ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) (cpt p.P.A3.fam3.base3.v0.embedding z)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact congrArg (· * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))) (twist_conj_base_embedding_eq p (z k))
  have hκ : κ ≠ 0 := by
    intro hκ0
    have h0 : ∀ y, (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y)) = 0 := by
      intro y
      apply hI
      intro b
      have := key p.P.A3.fam3.base3.μ0 y b
      rw [hκ0, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (hze _) (hc0 _))
    have i0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) := ⟨0, R0.pos⟩
    obtain ⟨y, hy⟩ := hwf.Pq_surj p.P.A3.fam3.base3.μ0 (Pi.single i0 1)
    have h1 := h0 y
    rw [hy] at h1
    have h2 := congrFun (hinj (h1.trans (map_zero _).symm)) i0
    simp [cpt] at h2
  let c0 : ℂ := κ⁻¹ * D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) * cTot a.ch p.P.A3.fam3.base3.μ0
  let Ψc : Matrix (Fin d.n) (Fin (p.S false).D) ℂ := Matrix.of fun b k =>
    c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))
  let ze' : Tup p → D.what₂.LL := fun t => ze t / ze p.P.A3.fam3.base3.μ0
  let r : Tup p → D.what₂.LL := fun t => ze' t * ∏ ij, d.rq t ij
  have hmain : ∀ t ∈ (Set.univ : Set (Tup p)),
      Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL = ((r t)⁻¹ • d.V t).map D.what₂.embLL := by
    intro t _
    have H : ∀ y : Fin ((Df p).nV t) → D.what₂.LL, ∀ b,
        (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b := by
      intro y b
      have e1 : Ψc.mulVec (cpt D.what₂.embLL (((p.S false).ι t).mulVec (((Df p).Pq t).mulVec y))) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← hrow, lin, Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, Ψc, Matrix.of_apply, cpt]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e3 := (TieModel.ratio_eq ht t).2
      have eL : (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← Matrix.mulVec_mulVec, ← cpt_mulVec, ← Matrix.mulVec_mulVec]
        exact e1
      have eR : (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (D.what₂.embLL (ze t) / D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) *
            (cTot a.ch t / cTot a.ch p.P.A3.fam3.base3.μ0))⁻¹ * D.what₂.embLL ((d.V t).mulVec y b) := by
        rw [← cpt_mulVec]
        show D.what₂.embLL ((((r t)⁻¹ • d.V t).mulVec y) b) = _
        rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [show r t = ze t / ze p.P.A3.fam3.base3.μ0 * ∏ ij, d.rq t ij from rfl, map_mul, map_div₀, e3]
        rfl
      have hP : psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
          κ * D.what₂.embLL ((d.V t).mulVec y b) / (D.what₂.embLL (ze t) * cTot a.ch t) :=
        eq_div_of_mul_eq (mul_ne_zero (hze t) (hc0 t)) (by rw [mul_comm]; exact key t y b)
      rw [eL, eR, hP]
      exact mul_eq_one_of_covolume_identity _ _ _ _ _ _ hκ (hze t) (hze _) (hc0 t) (hc0 _)
    ext b col
    have := H (Pi.single col 1) b
    have hs : cpt D.what₂.embLL (Pi.single col (1 : D.what₂.LL)) = Pi.single col 1 := by
      funext i; by_cases hi : i = col <;> simp [cpt, hi]
    rw [hs, Matrix.mulVec_single, Matrix.mulVec_single] at this
    simpa using this
  have hbij : Function.Bijective ((p.S false).ι p.P.A3.fam3.base3.μ0).mulVec := (hR0 ▸ R0.l1c).1 _
  obtain ⟨⟨Ψ, -, hΨ⟩, -⟩ := GlobalTheory.complex_matrix_descends_of_rational_on_tuple D.what₂.embLL d.n (p.S false).D (Df p).dQ
    (Df p).nV (p.S false).ι (Df p).Pq d.V r Set.univ p.P.A3.fam3.base3.μ0 Ψc trivial hbij
    (hwf.Pq_surj _) hmain
  refine ⟨ze', by simp only [ze']; exact div_self (hzK _), fun t => ?_, Ψ, fun t _ => ?_⟩
  · obtain ⟨n, hn, e⟩ := hz t
    obtain ⟨m, hm, e'⟩ := hz p.P.A3.fam3.base3.μ0
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    show (ze t / ze p.P.A3.fam3.base3.μ0) ^ (n * m) = 1
    rw [div_pow, pow_mul (ze t), e, one_pow, pow_mul' (ze _), e', one_pow, div_one]
  · refine (hΨ t trivial).trans ?_
    show _ = (∏ ij, d.rq t ij)⁻¹ • ((ze' t)⁻¹ • d.V t)
    rw [smul_smul, mul_inv, mul_comm]
theorem oneMap_of_bundle_setAt_kernel_conditions (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) (h1 : LinK) (h2 : InjK) (h3 : ConstK) (h4 : Formula2K) : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @Comparison₂ := by
  obtain ⟨CF0, hQ⟩ := hS.atPt (h1.and (h2.and (h3.and h4)))
  refine ⟨CF0, fun CF hCF => (hQ CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p hp q d hd => ?_⟩⟩
  obtain ⟨-, a, ht⟩ := hd
  obtain ⟨wf, R0, hR⟩ := hB p hp
  exact _root_.GlobalTheory.BigTop.Fun.exists_unit_root_ze_leafC_of_square_nonzero p hp d a ht wf ⟨R0, hR⟩ (q d.G d.W d.n a ht.ok)
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRowsStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | exact _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | (intros; apply _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions <;> assumption)
end
end
end
