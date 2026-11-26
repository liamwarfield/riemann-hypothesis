module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmall
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmall
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
namespace GlobalTheory.FrameRead
open Formalism.IndefR.Bridge
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Core
variable {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {l : ℕ} [Fact l.Prime]
end Core
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem reads_of_small_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ j P W hD _ w _ _ _ _ => ?_⟩⟩
  choose cs hcs using hD.lam
  exact ⟨false, fun τ => -cs τ, fun e0 io ev bs rk Lf _ kap chi hC hbs =>
    reads_rank p j w W.lam cs hcs e0 io ev bs rk Lf kap chi hC hbs⟩
end GlobalTheory.FrameRead
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmallStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readsAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  first | exact @_root_.GlobalTheory.FrameRead.reads_of_small_alt | exact _root_.GlobalTheory.FrameRead.reads_of_small_alt | (intros; apply _root_.GlobalTheory.FrameRead.reads_of_small_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermSt
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem permSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩
end GlobalTheory.FramePerm
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermStStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  first | exact @_root_.GlobalTheory.FramePerm.permSt_alt | exact _root_.GlobalTheory.FramePerm.permSt_alt | (intros; apply _root_.GlobalTheory.FramePerm.permSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRange
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRange
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HalfLabels
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]
end GlobalTheory.HalfLabels
namespace GlobalTheory.HalfLabels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem halfAt_inRange_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)
end GlobalTheory.HalfLabels
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRangeStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRange_halfAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  first | exact @_root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | exact _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt | (intros; apply _root_.GlobalTheory.HalfLabels.halfAt_inRange_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Comm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Comm
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeCommFrame
theorem comm_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → CommAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ p _ _ j P _ _ _ w _ _ _ => commAt_of p j P w⟩⟩
end GlobalTheory.HeckeCommFrame
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commAt_of_smallAt_in_range : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → CommAt p j P w := by
  first | exact @_root_.GlobalTheory.HeckeCommFrame.comm_alt | exact _root_.GlobalTheory.HeckeCommFrame.comm_alt | (intros; apply _root_.GlobalTheory.HeckeCommFrame.comm_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]
end Int
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pt
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem kapSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ _ _ p _ _ j P _ _ _ w _ _ _ => kapAt p j P w⟩⟩⟩
end Pt
end GlobalTheory.FrameOf
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRange_kapAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @_root_.GlobalTheory.FrameOf.kapSt_alt | exact _root_.GlobalTheory.FrameOf.kapSt_alt | (intros; apply _root_.GlobalTheory.FrameOf.kapSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
namespace GlobalTheory.TameStab
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Groups
variable {G Γ : Type} [Group G] [Group Γ]
end Groups
theorem tameSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt Formalism.MainNotions.Closed _root_.GlobalTheory.BigTop.EventuallyAtPoints
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS
end GlobalTheory.TameStab
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameStStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_at_of_small_at : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  first | exact @_root_.GlobalTheory.TameStab.tameSt_alt | exact _root_.GlobalTheory.TameStab.tameSt_alt | (intros; apply _root_.GlobalTheory.TameStab.tameSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRange
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRange
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelCharExp
open Formalism.BasicNotions.TH Formalism.IndefR.Lev
end GlobalTheory.LevelCharExp
end
namespace GlobalTheory.LevelCharExp
theorem chiAt_inRange_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ j P W _ _ w _ _ _ => ?_
  refine ⟨expOf (p.R.datVt j (p.R.mu w)), expOf_pos _, fun κ => ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (levEnv_chi_pow _ _ _ κ)
end GlobalTheory.LevelCharExp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRangeStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  first | exact @_root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | exact _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | (intros; apply _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameOf
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
theorem inRange_and_alt {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (h2 : _root_.GlobalTheory.ExpTie.InRangeAlt Q2) :
    _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x hx i p j P W w => Q1 Fm x hx i p j P W w ∧ Q2 Fm x hx i p j P W w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 h2 ⊢
  refine Closed.imp (Closed.and h1 h2) fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and h.1 h.2
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR =>
    ⟨(hx0 x hx hle i p hp).1 hM j P W hD hN w hw hR, (hx0 x hx hle i p hp).2 hM j P W hD hN w hw hR⟩⟩
theorem inRange_of_dict_imp {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i)
      (j : Fin (Fm.D x i).R.m) (P : Par) (W : Wts (Fm.D x i).what₂.Tau) (w : HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL)),
      Dict (Fm.L x i) j P W → Q1 Fm x hx i p j P W w → Q2 Fm x hx i p j P W w) : _root_.GlobalTheory.ExpTie.InRangeAlt Q2 := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 ⊢
  refine Closed.imp h1 fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR => f Fm x hx i p j P W w hD (hx0 x hx hle i p hp hM j P W hD hN w hw hR)⟩
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem frameSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' := by
  intro hS
  have h := _root_.GlobalTheory.FrameOf.inRange_and_alt hS (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_halfAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_kapAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.chiAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.tame_at_of_small_at
    (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.permAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.commAt_of_smallAt_in_range _root_.GlobalTheory.T.readsAt_of_smallAt))))))
  refine _root_.GlobalTheory.FrameOf.inRange_of_dict_imp h fun Fm x hx i p j P W w hD hq => ?_
  obtain ⟨hs, hh, hk, hc, ht, hp, hcm, hr⟩ := hq
  exact frameAt_of p j P W w hD.Nr (hh hs) (hk hs) (hc hs) (ht hs) (hp hs) (hcm hs) (hr hs)
end GlobalTheory.FrameOf
end
end
