module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemOfForall
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
namespace GlobalTheory.HeightCounting.Up.CoefficientAgreement
theorem atMem_of_forall' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
    (h : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c _ _ _
  exact h K B f T w Z Wt p0 t nch n c
end GlobalTheory.HeightCounting.Up.CoefficientAgreement
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemParametersRegularGap
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ParamsLayer
theorem parameters_gap_regular_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ ∀ (τ : (w.D Z).what₂.Tau) (n : ℕ), n + 1 < (w.D Z).R.r → 100 * ((w.D Z).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) n - Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) (n + 1) := by
  intro _ hL
  have e := (evG_of_ev GlobalTheory.Mem.RowsLed.ev_exists_sizeData_of_rows).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  refine EvG.imp e fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨L, -, hP⟩ := hK.1 B f T w Z Wt p0 t hO
  exact ⟨⟨L, hP⟩, (hK.2 (w.st Z) hO).1.gapR⟩
end GlobalTheory.HeightCounting.Up.ParamsLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameter_choice_and_lamAt_gap_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ ∀ (τ : (w.D Z).what₂.Tau) (n : ℕ), n + 1 < (w.D Z).R.r → 100 * ((w.D Z).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) n - Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) (n + 1) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt | exact _root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemExistsEigenvalueIndexLabeling
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdxAt
theorem exists_divisor_eigenvalueIndex_labeling_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  intro _ hL
  have e0 : EvLgG fun _ _ _ _ => True :=
    evG_good.imp fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint
  refine e0.imp fun K _ _ _ _ hK => ?_
  refine hK.imp fun B f T _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  refine ⟨GlobalTheory.Mem.Top.DivRec.x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange, GlobalTheory.eigIdxFiniteTypes _ _, ⟨fun σ => ?_⟩⟩
  have hc := (t.r.intersectionNumber_baseChange.ok.ok2.what₂ (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.μ0).comm
  let p := GlobalTheory.Mem.Top.DivRec.labOf t.r.Z t.r.intersectionNumber_baseChange σ
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ hc p.2⟩
end GlobalTheory.HeightCounting.Up.IdxAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigIdx_labeling_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemFrobeniusTracesAgree
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
open Formalism.BasicNotions.TH
namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement
set_option maxHeartbeats 1000000 in
theorem frobeniusTraces_agree_of_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, Nonempty (GlobalTheory.NJoin.Agree (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) c.a.all.gal.mt (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf).rep) := by
  intro _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c hNE _ _ hC Xd E labPi hb htup hg hf
  obtain ⟨m⟩ := hNE
  have ad := m.ad
  refine ⟨⟨t.r.Y.hF, ad.PV, fun j => (stdFrame_iff _ _).1 (ad.std j), fun j => (stdFrame_iff _ _).1 (t.r.Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (ad.eW μ hμ j).symm, ?_, ?_, fun σ => ?_⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact ad.rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := ad.wt μ hμ j h γ hγ he' ((ad.eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (ad.read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    rfl
  · exact Formalism.L2.NG.IsoRep.refl _
end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_agree_realOfRead_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, Nonempty (GlobalTheory.NJoin.Agree (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) c.a.all.gal.mt (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf).rep) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.StandardFrameAgreement.frobeniusTraces_agree_of_layer_alt | exact _root_.GlobalTheory.HeightCounting.Up.StandardFrameAgreement.frobeniusTraces_agree_of_layer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.StandardFrameAgreement.frobeniusTraces_agree_of_layer_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemUnramifiedComponentTied
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
theorem unramified_component_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  intro _ hL
  exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall' fun _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ =>
    goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ t.r.intersectionNumber_baseChange.ok.ok2
end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemCoefficientFieldsTied
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
namespace GlobalTheory.HeightCounting.Up.CoefficientAgreement
theorem coefficientField_tied_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  intro _ hL
  exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall' fun K B f T w Z Wt p0 t nch n c => t.r.z.lev.C
end GlobalTheory.HeightCounting.Up.CoefficientAgreement
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefField_eq_TC_cf_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemHeckeCharacterTupleLayer
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up
theorem heckeCharacter_tuple_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ n _ => ∀ μ, Used0 (w.D Z) μ → t.r.z.R.toLevCh.xiH (t.r.Y.tupT μ) = n.tp.xi μ := by
  intro _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ μ hμ => ?_
  have a := t.r.z.lev.xiH (t.r.Y.tupT μ)
  have b := t.r.Y.tupTie μ hμ
  have d := congrFun n.xi μ
  refine a.trans (Eq.trans ?_ d.symm)
  exact congrArg w.I.xi ((t.r.tup_ix _).symm.trans b)
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiH_tupT_eq_tp_xi_of_used0_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ n _ => ∀ μ, Used0 (w.D Z) μ → t.r.z.R.toLevCh.xiH (t.r.Y.tupT μ) = n.tp.xi μ := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt | exact _root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemInertialTypesAtMember
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.TypesAt
theorem inertialTypes_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  intro _ hL
  refine EvG.imp evG_good fun K _ _ _ _ _ => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T _ _ _ _ _ w Z Wt p0 t nch n xd c _ _ _
  exact typesTrue_rows t
end GlobalTheory.HeightCounting.Up.TypesAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typesTrue_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open RealOfReading
theorem isTied_of_layer_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefField_eq_TC_cf_at_member_of_published_inputs hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.xiH_tupT_eq_tp_xi_of_used0_at_member hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_parameter_choice_and_lamAt_gap_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.typesTrue_at_member_of_published_inputs hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_eigIdx_labeling_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.nonempty_agree_realOfRead_at_member hP hL) (_root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member hP hL)))))))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hC, htup, ⟨hPar, hGap⟩, hTT, ⟨Xd, E, ⟨labPi⟩⟩, hAg, hE0⟩
  have hg : GlobalTheory.LiftRows.Given t.r.z.R.toRealDat t.r.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1, hPar, t.r.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ t.r.z.pins.char.base.lev hTT, t.r.z.pins.keep.guard, hGap⟩
  obtain ⟨ag⟩ := hAg hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP
  obtain ⟨T0, hT0, hR⟩ := _root_.GlobalTheory.HeightCounting.Up.RealOfReading.exists_linked_data_of_agreement P (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi
    t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP) hPin.cf_eq hPin.C_eq hPin.tp_eq
    hPin.M_eq (hPin.rep_eq.trans c.row.rep_eq) ag (hE0 hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP)
  exact ⟨T0, by rw [hT0]; exact hPin, hR⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linked_data_pinned_at_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt <;> assumption)
end
end
