module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinalityStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinalityAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastStepIntegrableOn
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastStepIntegrableOn
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem lastStep_integrableOn_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv F Q x g
  have hC := hP.bot.hyp.2.2.2.1
  have hω : IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' _ _ (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) :=
    weil_transport ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) (hC.chain.ωX W.P.A3.A.μ0) (j + 1) (idx_top h)
  obtain ⟨c1, hc1⟩ := hC.lev.βY (j + 1) (by omega)
  obtain ⟨c2, hc2⟩ := hC.lev.βX
  have hv' : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' v :=
    (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc1) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc2) hc1.1 hc2.1 hv
  have hf := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hC.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) hv' Q
  have hν := hC.models.νX W.P.A3.A.μ0
  have key := GlobalTheory.Hk3.StepX.integ_X hω hf (F.1 x)
    (multT_apply_continuous _ _ _ _ F.1 F.2 x) (multT_apply_left _ _ _ _ F.1 F.2 x) _ hν.1.1 _ hν.2 g 1
  simpa only [mul_one] using key
end GlobalTheory.BaseChain
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastStepIntegrableOnStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_step_vector_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  first | exact @_root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | exact _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | (intros; apply _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
theorem stepX_isIo_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hcard : Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H ≠ 0 := by
    have hf' : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    exact Nat.card_pos.ne'
  have hcH : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
    simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality]
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · have h1 := _root_.GlobalTheory.T.top_step_vector_property_alt W hP j h _ ((hf.row W.P.A3.A.μ0).vT j h) F φ v g
    unfold IntegrableOn at h1 ⊢
    change Integrable _ ((_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0).restrict ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0))
    rw [Measure.restrict_smul]
    exact h1.smul_measure hcH
  · obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g W.P.A3.A.μ0 j h F
    obtain ⟨h'', he⟩ := (hf.row W.P.A3.A.μ0).ioT j h F
    have e1 := congrFun (hL _ ((hf.row W.P.A3.A.μ0).vT j h) φ v) g
    have key : ∀ X : ℂ, (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * X) = X := by
      intro X
      have e3 : (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal = ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℝ))⁻¹ := by
        simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality, ENNReal.toReal_inv]
      have hc : ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard
      rw [e3, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [inv_mul_cancel₀ hc, one_mul]
    change ∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, _ ∂(_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
      ((f.row W.P.A3.A.μ0).ioT j h F).1 (f.c.ItT j h φ v) g
    rw [setIntegral_smul_measure_complex, he]
    have e2 : (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row W.P.A3.A.μ0).vT j h) φ) * F.1 v y ∂(_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
        (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * (ioXT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h ⟨F.1, h''⟩).1 (f.c.ItT j h φ v) g := e1
    exact (congrArg (fun z : ℂ => (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • z) e2).trans (key _)
end GlobalTheory.BaseChain
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_top_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  first | exact @_root_.GlobalTheory.BaseChain.stepX_isIo_alt | exact _root_.GlobalTheory.BaseChain.stepX_isIo_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepX_isIo_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYIntegrableAndEqStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYIntegrableAndEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BaseChain.stepY_integrable_and_eq_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (t) (j) (hj : j + 1 < D.R.m) (F : CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) (hF : F.1 ∈ (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) (v) (hv : IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v) (Q x g) :
  IntegrableOn (fun h => thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g h (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ∧
  (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1), thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) * F.1 x y ∂((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1))) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) g := by
  have hio : Lift.IsIo ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j)
      ((_root_.GlobalTheory.Fam.pk_z W).ItY j) ((_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).CC t j) ((_root_.GlobalTheory.Fam.pk_z W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.T.exists_level_elements_step_vector_alt W hW t j hj
  rw [hsum v hv Q]
  simp_rw [GlobalTheory.BaseChain.thetaKO_sum_smul_act]
  have hint : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), IntegrableOn (fun h => (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), ∫ h in (_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1), (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h ∂(_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) =
      ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, _root_.GlobalTheory.T.chain_projection_level_character_alt W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul]
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BaseChain.stepY_isIo_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hrow := hf.row W.P.A3.A.μ0
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  have hc : Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H ≠ 0 := Nat.card_pos.ne'
  have hne : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hc)
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have hI := (_root_.GlobalTheory.BaseChain.stepY_integrable_and_eq_alt W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).1.smul_measure hne
    rw [← Measure.restrict_smul] at hI
    exact hI
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have e := (_root_.GlobalTheory.BaseChain.stepY_integrable_and_eq_alt W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).2
    have hk : (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) = 1 := by
      rw [Complex.real_smul, _root_.GlobalTheory.BaseChain.inverseLevelCardinality, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hc)]
    show (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 (j + 1), thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((f.row W.P.A3.A.μ0).vP j) φ) * F.1 v y ∂(_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 (j + 1))) = ((f.row W.P.A3.A.μ0).io j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ v) g
    rw [hio, Measure.restrict_smul, integral_smul_measure]
    exact (congrArg (fun z => (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • z) e).trans (by rw [← smul_mul_assoc, hk, one_mul])
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_step_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).io := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_isIo_alt | exact _root_.GlobalTheory.BaseChain.stepY_isIo_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_isIo_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndIt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopComb
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopComb
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopConv
variable {D : D7}
end GlobalTheory.TopConv
end
noncomputable section
namespace GlobalTheory.TopConv
set_option maxHeartbeats 1000000 in
theorem top_comb_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv
  have hLev := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hbY⟩ := hLev.βY (j + 1) (by omega)
  obtain ⟨cX', hbX⟩ := hLev.βX
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have hr : (Yc D (j + 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY n) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY n) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 n (_root_.GlobalTheory.Fam.pk_z W).triv) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m)
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (_root_.GlobalTheory.Fam.pk_z W).vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact W.Q.charW.base.chain.vX _
  have hX := key (j + 1) (idx_top h)
  obtain ⟨d₁, hd₁, e₁⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hX
  obtain ⟨d₂, hd₂, e₂⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hv
  have hv0 : v ≠ 0 := (GlobalTheory.Chain.StepVac.stepVec_vac sdY sdX hr hv).2.1
  have hspan := comb_mem_span (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₂) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)
  rw [← e₂] at hspan
  have hvac := GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hv.1 sdY sdX hspan hv0
  obtain ⟨b, hb, hbv⟩ := exists_finComb_of_mem_span _ hvac
  obtain ⟨c, hc, hcc⟩ := isFinComb_comp (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₁) hb
  refine ⟨c, hc, ?_⟩
  rw [hcc, hbv]
  exact e₁.symm
end GlobalTheory.TopConv
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCombStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_step_vector_theta_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  first | exact @_root_.GlobalTheory.TopConv.top_comb_alt | exact _root_.GlobalTheory.TopConv.top_comb_alt | (intros; apply _root_.GlobalTheory.TopConv.top_comb_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndIt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChainTop
variable {D : D7}
end GlobalTheory.BaseChainTop
namespace GlobalTheory.BaseChainTop
theorem theta_and_it_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j h
  have hC := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hP.ex
  have hvT := (hR.row W.P.A3.A.μ0).vT j h
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvT.1.2.inf
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' ((f.row W.P.A3.A.μ0).vT j h) :=
    GlobalTheory.VecTheta.isThetaFunO_stepVec hvT
  have key : ∀ n (e : D.R.m - 1 = n),
      IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) ∧
      IsItW (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e)
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e))
        (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact ⟨hC.chain.ωX _, hC.chain.ItX _⟩
  obtain ⟨hW', hI'⟩ := key (j + 1) (idx_top h)
  obtain ⟨b, hb, hbv⟩ := _root_.GlobalTheory.T.top_step_vector_theta_alt W hP j h _ hvT
  exact ⟨fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW'.std hθ _ _ _ _ hth φ, isItW_of_comb hW' hθ hth hb hbv hI'⟩
end GlobalTheory.BaseChainTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndItStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_top_theta_functions_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  first | exact @_root_.GlobalTheory.BaseChainTop.theta_and_it_alt | exact _root_.GlobalTheory.BaseChainTop.theta_and_it_alt | (intros; apply _root_.GlobalTheory.BaseChainTop.theta_and_it_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYWeilVec
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYWeilVec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem stepY_weil_vec_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hC := hW.bot.hyp.2.2.2.1
  have hQ : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun PP => _root_.GlobalTheory.MiTop.not_mem_Q_base' W PP
  refine ⟨hC.chain.ωY W.P.A3.A.μ0 j hj, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, (_root_.GlobalTheory.Fam.pk_z W).vac j, ?_⟩
  have h := (hf.row W.P.A3.A.μ0).vP j hj
  rw [hQ] at h
  exact h
end GlobalTheory.BaseChain
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYWeilVecStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_step_weil_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).f := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_weil_vec_alt | exact _root_.GlobalTheory.BaseChain.stepY_weil_vec_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_weil_vec_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepXWeilVec
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepXWeilVec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem stepX_weil_vec_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1 + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1 + 1)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1 + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hm : j + 1 + 1 = D.R.m := by omega
  have hC := hP.bot.hyp.2.2.2.1
  have hQ : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    exact _root_.GlobalTheory.MiTop.not_mem_Q_base' W PP
  refine ⟨?_, ?_⟩
  · have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
      rintro n rfl
      exact hC.chain.ωX W.P.A3.A.μ0
    have := key _ (idx_top h)
    simp only [_root_.GlobalTheory.BaseChain.com_z, _root_.GlobalTheory.BaseChain.stageOfSpaceY, _root_.GlobalTheory.BaseChain.stageOfSpaceX, _root_.GlobalTheory.BaseChain.transitionToSpaceX, GlobalTheory.ChainOnto.Com.chS, GlobalTheory.ChainOnto.Com.chT]
    rw [hm]
    exact this
  · refine ⟨(_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, vacT (_root_.GlobalTheory.Fam.pk_z W) j h, ?_⟩
    have hv := (hf.row W.P.A3.A.μ0).vT j h
    rw [hQ] at hv
    simp only [_root_.GlobalTheory.BaseChain.com_z, _root_.GlobalTheory.BaseChain.stageOfSpaceY, _root_.GlobalTheory.BaseChain.stageOfSpaceX, _root_.GlobalTheory.BaseChain.transitionToSpaceX]
    rw [hm]
    exact hv
end GlobalTheory.BaseChain
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepXWeilVecStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_top_weil_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1 + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1 + 1)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1 + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).f := by
  first | exact @_root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | exact _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevChiDatYtBase
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevChiDatYtBase
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem levS_datYt_base_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) = levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  have e : Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
    refine Subgroup.ext fun x => ?_
    show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
    unfold LevCh.datYt LevCh.dat0
    rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B x]
    rfl
  unfold levS Lev.levG
  rw [e]
theorem levChi_datYt_zero_eq_dat0 (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  funext k
  unfold Lev.levChi LevCh.datYt LevCh.dat0
  rw [levFn_datY_noQ ((_root_.GlobalTheory.Fam.pk_z W).βY 0) Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B]
theorem initial_tuples_mem_stageY_zero_CC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ∈ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).CC (_root_.GlobalTheory.BaseChain.com_z W) := by
  intro D L hT Gi Gl Kc Yd cX ex W _ T hT0
  show T ∈ MultT (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
    (Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
  rw [_root_.GlobalTheory.BaseChain.levS_datYt_base_alt W, _root_.GlobalTheory.BaseChain.levChi_datYt_zero_eq_dat0 W]
  exact hT0
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevChiDatYtBaseStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stageY_zero_cc_of_mem_zero_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ∈ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).CC (_root_.GlobalTheory.BaseChain.com_z W) := by
  first | exact @_root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC | exact _root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC | (intros; apply _root_.GlobalTheory.BaseChain.initial_tuples_mem_stageY_zero_CC <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYThetaFunIsItW
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYThetaFunIsItW
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7}
theorem stepY_thetaFun_isItW_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j hj
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have hj' : j < D.R.m := by omega
  have dS : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY j hj')
  have dT : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY (j + 1) hj)
  have hP' := (hR.row W.P.A3.A.μ0).vP j hj
  have hY := hC.chain.vY W.P.A3.A.μ0 j hj
  have hω := hC.chain.ωY W.P.A3.A.μ0 j hj
  have hθ := hC.models.inf
  obtain ⟨vth, vne, -⟩ := GlobalTheory.InnerSteps.stepVec_vac dS dT (rank_Yc_le_succ j) hP'
  refine ⟨fun φ => GlobalTheory.FockTheta.ptStable D _ _ hP'.1.1 hθ _ _ _ _ _ _ _ φ vth, ?_⟩
  have h0 := GlobalTheory.Grid.isItW_of_mem_span hω hθ hP'.1.2.theta (GlobalTheory.Grid.stepVec_mem_span dS dT hY)
    (hC.chain.ItY W.P.A3.A.μ0 j hj)
  exact GlobalTheory.Grid.isItW_of_mem_span hω hθ vth (GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hP'.1 dS dT (GlobalTheory.Grid.stepVec_mem_span dS dT hP') vne) h0
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepYThetaFunIsItWStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_step_theta_functions_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_thetaFun_isItW_alt | exact _root_.GlobalTheory.BaseChain.stepY_thetaFun_isItW_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_thetaFun_isItW_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkOntoOfOntoAll
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
theorem stepY_is_alt {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) (j : ℕ) (hj : j + 1 < D.R.m) :
    (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).Is (j + 1) :=
  ⟨(_root_.GlobalTheory.T.base_chain_step_weil_datum_alt W u f hP hf j hj).1, (_root_.GlobalTheory.T.base_chain_step_weil_datum_alt W u f hP hf j hj).2, (_root_.GlobalTheory.T.base_chain_step_theta_functions_alt W u f hP hf j hj).1,
    (_root_.GlobalTheory.T.base_chain_step_theta_functions_alt W u f hP hf j hj).2, _root_.GlobalTheory.T.base_chain_step_theta_lift_alt W u f hP hf j hj⟩
theorem chainX_is_succ_succ {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) : (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).Is (j + 1 + 1) :=
  ⟨(_root_.GlobalTheory.T.base_chain_top_weil_datum_alt W u f hP hf j h).1, (_root_.GlobalTheory.T.base_chain_top_weil_datum_alt W u f hP hf j h).2, (_root_.GlobalTheory.T.base_chain_top_theta_functions_alt W u f hP hf j h).1,
    (_root_.GlobalTheory.T.base_chain_top_theta_functions_alt W u f hP hf j h).2, _root_.GlobalTheory.T.base_chain_top_theta_lift_alt W u f hP hf j h⟩
theorem reach_stageY_dn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hf : f.RowOK) :
    ∀ k, k + 1 ≤ D.R.m → Reach (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0) k (_root_.GlobalTheory.BaseChain.stageOfSpaceY W k) ((f.t W.P.A3.A.μ0).dn k)
  | 0, _ => Reach.zero
  | k + 1, hk => Reach.step (reach_stageY_dn f hP hf k (by omega)) (_root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt W hP (k + 1) (by omega)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f k)
      (_root_.GlobalTheory.BaseChain.stepY_is_alt f hP hf k (by omega))
theorem linkOnto_of_ontoAll_third_place_series : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word),
    _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.ChainOnto.OntoAll D → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkSurjective f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP hO f hf n h T hT
  have e : 2 * n + 1 + 1 = D.R.m := by omega
  have hX : (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) (2 * n + 1 + 1) := e ▸ _root_.GlobalTheory.T.baseChain_stageX_is_of_pkHyp W hP
  have hR := Reach.step (_root_.GlobalTheory.BaseChain.reach_stageY_dn f hP hf (2 * n + 1) (by omega)) hX (_root_.GlobalTheory.BaseChain.transitionToSpaceX f (2 * n) h) (_root_.GlobalTheory.BaseChain.chainX_is_succ_succ f hP hf (2 * n) h)
  obtain ⟨G, hG⟩ := hO hP.gap (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.T.baseChain_com_z_is_of_pkHyp W hP) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0) (_root_.GlobalTheory.T.baseChain_stageY_is_of_pkHyp_of_lt W hP 0 (by omega)) (2 * n + 1 + 1) (by omega)
    _ _ hR ⟨T, _root_.GlobalTheory.T.mem_stageY_zero_cc_of_mem_zero_set W hP T hT⟩
  exact ⟨G, congrArg Subtype.val hG⟩
end GlobalTheory.BaseChain
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkOntoOfOntoAllStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkOnto_of_ontoAll' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.ChainOnto.OntoAll D → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkSurjective f := by
  first | exact @_root_.GlobalTheory.BaseChain.linkOnto_of_ontoAll_third_place_series | exact _root_.GlobalTheory.BaseChain.linkOnto_of_ontoAll_third_place_series | (intros; apply _root_.GlobalTheory.BaseChain.linkOnto_of_ontoAll_third_place_series <;> assumption)
end
end
