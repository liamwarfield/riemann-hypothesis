module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairForm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitVectorLineConjugate
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitVectorLineConjugate
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.LineV
open GlobalTheory.PiTensorInner
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop
theorem unit_vector_line_conjugate_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB v₀ v hv hn T hTm hT0 φ hφ hst
  obtain ⟨-, hθ, -, hM, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hMt : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
    have := hM 1 (one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  obtain ⟨⟨j, hj, hjT⟩, -⟩ := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (show GA D (D.sp.Y 0) from W.Q.tS) v (by simp) hθ hB.gap hB.idE hMt hv
  obtain ⟨T', hT'⟩ := hj.2 ⟨star φ, hst⟩
  have h1 := hjT T'
  rw [hT'] at h1
  have he : evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX W.S.X]
      evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T'.1 (PiTensorProduct.tprod ℂ v)) := by
    filter_upwards [hφ, h1, Lp.coeFn_star φ] with x a1 a2 a3
    rw [← a1]
    have a4 := a3.symm.trans a2
    simpa using congrArg star a4
  exact LineV.line_of_eq hCR hθ hTm T'.2 v₀ v hn hT0 (LineV.eq_of_evS_ae W.S.X W.Q.instEq _ hTm T'.2 v₀ v he)
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitVectorLineConjugateStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_vector_rows_conjugate_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  first | exact @_root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt | exact _root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt | (intros; apply _root_.GlobalTheory.MiTop.unit_vector_line_conjugate_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairForm
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.PairingL2
open _root_.Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation _root_.Formalism.L2.SG.RowsJoinPinned
variable {D : D7}
end GlobalTheory.MiTop.PairingL2
namespace GlobalTheory.MiTop.PairingL2
open _root_.Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation _root_.Formalism.L2.SG.RowsJoinPinned
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem pwOf_op_ramCrd_eq_puFun (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u w : D.what₂.Word) (hwu : w = u) (hc : W.P.I.wU w = W.P.I.wU u)
    (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (hT : _root_.GlobalTheory.MiTop.IsColumnForm W u T (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x)) :
    (((_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin w).op (ramCrd (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) x) : HHX W.S.X) : L2X W.S.X) =
      PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T := by
  subst hwu
  have hi : ∀ i : Fin (W.P.Dc.a (W.P.I.wU w)), Fin.cast (congrArg W.P.Dc.a hc).symm i = i := fun i => Fin.ext rfl
  have hfun : (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) =
      (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) := by
    funext i
    exact congrArg (fun k => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single k (1 : D.what₂.LL))))) (hi i)
  rw [hfun]
  have hr : Fintype.linearCombination ℂ (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) x =
      D.eMu w (_root_.GlobalTheory.MiTop.columnOfCoordinates W w x) := by
    refine (Fintype.linearCombination_apply ℂ _ x).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.MiTop.columnOfCoordinates, map_sum, map_smul]
  refine op_eq (_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin w) _ T ?_
  show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr w) W.S.Y.hK T = _
  refine hT.trans ?_
  show _ = ((Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ _ x) : (D.mem w).A.Mu0) : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)
  exact congrArg (fun z : (D.mem w).A.Mram => (z : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)) hr.symm
end GlobalTheory.MiTop.PairingL2
namespace GlobalTheory.MiTop.PairingL2
open _root_.Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation _root_.Formalism.L2.SG.RowsJoinPinned
theorem pairForm_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → _root_.GlobalTheory.MiTop.PairingFormCondition W v := by
  intro hDS hCusp D L hT Gi Gl Kc Yd cX ex W hB v hv
  have hM := (_root_.GlobalTheory.MiTop.botHyp_match_alt W hB).2.2.2.2.2
  obtain ⟨v₀, hv₀, hF⟩ := exists_eval (W.Q.seeEval hB.see.2) W.Q.instEq W.Q.ιS_eq
  have key : ∃ l : ℂ, l ≠ 0 ∧ ∀ e : W.Q.Rl.HE.H,
      W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
        _root_.GlobalTheory.MiTop.rowFormOfVector W e (PiTensorProduct.tprod ℂ v₀) = l • _root_.GlobalTheory.MiTop.rowFormOfVector W e (PiTensorProduct.tprod ℂ v) := by
    by_cases hl : ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v
    · obtain ⟨l, hl0, hl⟩ := hl
      exact ⟨l, hl0, fun e _ => (congrArg (_root_.GlobalTheory.MiTop.rowFormOfVector W e) hl).trans ((_root_.GlobalTheory.MiTop.rowFormOfVector W e).map_smul l _)⟩
    · refine ⟨1, one_ne_zero, fun e he => ?_⟩
      by_cases h0 : _root_.GlobalTheory.MiTop.rowFormOfVector W e = 0
      · rw [h0]
        exact (smul_zero (1 : ℂ)).symm
      · obtain ⟨F, h1, h2, -⟩ := hF ⟨W.Q.Rl.HE.e e, he⟩
        exact absurd (_root_.GlobalTheory.T.unit_vector_rows_conjugate_alt hDS hCusp W hB v₀ v hv hv₀ (_root_.GlobalTheory.MiTop.rowFormOfVector W e) (hM e he) h0 F h1 h2) hl
  obtain ⟨l, hl0, hl⟩ := key
  refine ⟨starRingEnd ℂ (W.Q.uS * (W.Q.κS : ℂ)) * l, mul_ne_zero ?_ hl0, ?_⟩
  · have hu : W.Q.uS ≠ 0 := by
      intro h
      have := W.Q.uS_norm
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact (map_ne_zero _).2 (mul_ne_zero hu (Complex.ofReal_ne_zero.2 W.Q.seeK.1.ne'))
  intro e he u m hm x x' hx T b hTc hP
  obtain ⟨φ, hφ, rfl⟩ := hP
  refine (inner_join (twQ W.P) W.Dcf W.Spf (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs W.P.Zs W.Q.zs W.P.Dc W.Q.dc W.S.Y.hK W.S.G W.Q.wdD
    (fun y => _root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD y)) W.Q.bR (W.Q.sp.trans W.Q.spPin) W.Q.sEE W.Q.sEEc W.Q.sEEj e m (W.P.I.wU u) hm
    x' x hx.symm).trans (congrArg (cj (twQ W.P)) ?_)
  obtain ⟨F, h1, -, h3⟩ := hF ⟨W.Q.Rl.HE.e (Tw.out e), he⟩
  have hz := (congrArg (fun b => (((_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd b x) : HHX W.S.X) : L2X W.S.X))
    (funext (hB.pins.bR_read (W.P.I.wU u)))).trans
    (_root_.GlobalTheory.MiTop.PairingL2.pwOf_op_ramCrd_eq_puFun W u (W.Q.wdD (W.P.I.wU u)) (W.Q.wdD_wU u) (W.Q.wU_wdD (W.P.I.wU u)) x T hTc)
  refine Eq.trans ?_ (inner_smul_star W.Q.instEq _ _ _ l (W.Q.uS * (W.Q.κS : ℂ)) (hl (Tw.out e) he) F φ _ h1 hφ _ _ h3 hz)
  exact congrArg (fun y => ⟪Tw.out y, (_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd (W.Q.bR (W.P.I.wU u)) x)⟫_ℂ)
    (W.Q.seeDef e he)
end GlobalTheory.MiTop.PairingL2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairFormStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairForm_of_conjVec_of_botHyp : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → _root_.GlobalTheory.MiTop.PairingFormCondition W v := by
  first | exact @_root_.GlobalTheory.MiTop.PairingL2.pairForm_alt | exact _root_.GlobalTheory.MiTop.PairingL2.pairForm_alt | (intros; apply _root_.GlobalTheory.MiTop.PairingL2.pairForm_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwo
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamified
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpCEqSum
set_option synthInstance.maxHeartbeats 200000

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.MiTop.CenIsom
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
open Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.DIV
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
set_option maxHeartbeats 1000000 in
theorem ipC_colDictL_eq_sum_inner_shP (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)
theorem ipC_colDictL_rtr_eq (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u P P').trans (Eq.trans ?_ (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'
end GlobalTheory.MiTop.CenIsom
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamified
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Mi.CenAct in
theorem GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB u d z hP
  have hδ : ∀ k : Hfin W.S.X u, (d.B.toH d.a).2 * k = k * (d.B.toH d.a).2 := toH_snd_comm d.B hP.cen
  have hta : d.B.toH d.a = (1, (d.B.toH d.a).2) := Prod.ext (toH_fst d.B hP.fin) rfl
  generalize (d.B.toH d.a).2 = δ at hδ hta
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  let col : D.what₂.Mu u →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    e.symm.toLinearMap ∘ₗ (Submodule.inclusion hram) ∘ₗ (D.eMu u).toLinearMap
  have hcol : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (col φ) =
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  let mv : Cu W.S.X u W.S.Y.hK →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    (Formalism.L2.SG.ColDict.rtr W.S.X δ).restrict (fun T hT => rtr_mem_Cu W.S.Y.hK hδ hT)
  have hmv : ∀ T, (mv T).1 = Formalism.L2.SG.ColDict.rtr W.S.X δ T.1 := fun T => rfl
  have hmem : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) ∈ (D.mem u).A.Mram := fun φ =>
    GlobalTheory.MiTop.CenIsom.ram_rtr (W.S.tr u) W.S.Y.hK (W.S.lev u) (W.S.into u) (W.S.bij u) δ hδ (col φ) (mv (col φ)) (hmv _) (by rw [hcol]; exact (D.eMu u φ).2)
  let g0 : D.what₂.Mu u →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
    Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK ∘ₗ mv ∘ₗ col
  let fL : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := (D.eMu u).symm.toLinearMap ∘ₗ g0.codRestrict _ hmem
  have hfL : ∀ φ, ((D.eMu u (fL φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) := fun φ => by
    have h1 : D.eMu u (fL φ) = ⟨Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)), hmem φ⟩ :=
      (D.eMu u).apply_symm_apply _
    rw [h1]
  clear_value fL g0 mv col e
  have hinner : ∀ x y, ⟪fL x, fL y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by
    refine ((D.eMu_isom u (fL x) (fL y)).trans ?_).trans (D.eMu_isom u x y).symm
    refine (congrArg₂ ((D.fm u).ipC 0) (hfL x) (hfL y)).trans ?_
    refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_rtr_eq W.S hB.fin u δ hδ (col x) (col y) (mv (col x)) (mv (col y)) (hmv _) (hmv _)).trans ?_
    exact congrArg₂ ((D.fm u).ipC 0) (hcol x) (hcol y)
  let Li := fL.isometryOfInner hinner
  haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
  haveI : FiniteDimensional ℂ (D.mem u).A.Mram := Submodule.finiteDimensional_of_le hram
  haveI : FiniteDimensional ℂ (D.what₂.Mu u) := LinearEquiv.finiteDimensional (D.eMu u).symm
  have hsurj : Function.Surjective Li := (LinearMap.injective_iff_surjective (f := Li.toLinearMap)).1 Li.injective
  refine ⟨LinearIsometryEquiv.ofSurjective Li hsurj, ?_⟩
  intro φ C C₀ hC hC₀ ξ
  have e1 : C = mv (col φ) := (W.S.bij u).1 (hC.trans (hfL φ))
  have e2 : C₀ = col φ := (W.S.bij u).1 (hC₀.trans (hcol φ).symm)
  rw [e1, e2]
  funext g
  simp only [SBes.colForm, rTrans]
  rw [hmv]
  have h4 : d.B.toH (g * d.a⁻¹) * (1, δ) = d.B.toH g :=
    (congrArg (fun y => d.B.toH (g * d.a⁻¹) * y) hta.symm).trans
      ((GlobalTheory.Core.Mi.CenAct.toH_mul d.B _ _).symm.trans (congrArg d.B.toH (inv_mul_cancel_right g d.a)))
  exact (congrArg ((col φ).1 ξ) h4).symm
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamifiedStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  first | exact @_root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | exact _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | (intros; apply _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwo
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk
noncomputable section
namespace GlobalTheory.MiTop.BotTwo
variable {D : D7}
end GlobalTheory.MiTop.BotTwo
set_option maxHeartbeats 1000000 in
open GlobalTheory.MiTop.BotTwo in
theorem GlobalTheory.MiTop.botRel_of_pin_of_mem_center : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u), d.Pin z → _root_.GlobalTheory.MiTop.BottomRelation W z d := by
  intro _ hCR D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc u d hP
  obtain ⟨-, hθ, hψ, hMatch, hχ, -⟩ := _root_.GlobalTheory.MiTop.botHyp_match_alt W hB
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin W hB u d z hP
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D W.S.X W.Q.instEq u W.Q.Rl.ψ d.B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK W.Q.Rl.θ d.a₀
    hθ hB.idE hP.adapted hP.h0 (hB.hyp.2.1 u)
  have hRS := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D W.S.X W.Q.instEq W.Q.Rl.θ hθ hB.idE
  obtain ⟨c, hc⟩ := GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y hψ (hB.fin.inHH u)
  have hMt := hMatch z hzf hzc
  have hf1 : (iotaX W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS))).1 = 1 := (hRS.1 _).1 hMt.1
  have hcont : ∀ (C : Cu W.S.X u W.S.Y.hK) ξ', IsContAut (D.sp.X 0) (d.B.colForm C.1 ξ') := fun C =>
    (GlobalTheory.Core.Mi.PhCol.ph_colForm D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y.hK C).1
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  have hcol : ∀ φ : D.what₂.Mu u, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK
      (e.symm (Submodule.inclusion hram (D.eMu u φ))) = (D.eMu u φ).1 := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  have L1 : ∀ (φ : D.what₂.Mu u) (C : Cu W.S.X u W.S.Y.hK), _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ y v,
      d.per φ T y v = _root_.GlobalTheory.MiTop.realCharacter W d.k * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) := by
    intro φ C hC T hT y v
    have hC₀ : _root_.GlobalTheory.MiTop.IsColumnForm W u (e.symm (Submodule.inclusion hram (D.eMu u φ))) φ := hcol φ
    have e1 : (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y =
        fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹) := by
      rw [← hcol φ]
      funext g
      rw [hξ _ y g, hR φ C _ hC hC₀ (ξ y)]
      simp only [rTrans]
      congr 1
      rw [mul_assoc, mul_inv_rev, (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hP.cen) d.a₀⁻¹)]
    have e2 : rTrans (embA d.B.d d.B.o (d.a₀ * d.a)) (rTrans d.b (T v)) =
        _root_.GlobalTheory.MiTop.realCharacter W d.k • rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v) := by
      funext g
      simp only [rTrans, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc g, hP.eq]
      refine Eq.trans (congrArg (T v) ?_) (lev_multT hT v hP.lev
        (g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) : GA D (D.sp.Y 0)))
      change g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)) =
        g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) * d.k
      rw [mul_assoc g, mul_assoc ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))]
    have ea : rTrans (d.a₀ * d.a) (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹)) = d.B.colForm C.1 (ξ y) := by
      funext g; simp only [rTrans, mul_inv_cancel_right]
    have hsh := GlobalTheory.Core.Mi.per_rTrans D W.Q.Rl.ψ D.R.rS d.B.lev (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹))
      (rTrans d.b (T v)) (d.a₀ * d.a) hψ (contAut_rTrans _ (hcont C (ξ y))) (contAut_rTrans _ (contAut_multT hT v))
    rw [ea] at hsh
    unfold _root_.GlobalTheory.MiTop.BottomData.per
    rw [e1, ← hsh, ← per_smul_f]
    exact congrArg _ e2
  refine ⟨R, ?_⟩
  intro φ φ' T hT T' hT' α α' hrel v C C' b b' hC hC' hb hb'
  have hrelξ : ∀ y v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro y v
    have h0 := hrel y v
    rw [L1 φ C hC T hT, L1 φ' C' hC' T' hT'] at h0
    refine (mul_eq_zero.1 ?_).resolve_left (hχ _ hP.lev)
    rw [← h0]; ring
  have hrelAll : ∀ ξ' v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro ξ' v
    have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hlin : ∀ C₁ : Cu W.S.X u W.S.Y.hK, d.B.colForm C₁.1 ξ' = ∑ i ∈ cf.support, cf i • d.B.colForm C₁.1 (ξ i) := by
      intro C₁
      rw [← hcf]
      funext g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    rw [hlin C, hlin C',
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT v)) _ cf.support cf
        (fun i => d.B.colForm C.1 (ξ i)) (fun i _ => hcont C (ξ i)),
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT' v)) _ cf.support cf
        (fun i => d.B.colForm C'.1 (ξ i)) (fun i _ => hcont C' (ξ i)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hrelξ i v
    linear_combination cf i * this
  have hσ : ∀ y : W.S.X.B.I.Ginf, ∃ σ : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] SmT (W.Q.Rl.MY 0), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ x,
      T (σ x) = rTrans ((iotaX W.S.X W.Q.instEq).symm (y, 1)) (T x) := by
    intro y
    obtain ⟨σ, hσ⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D W.Q.Rl.θ (D.sp.Y 0) _ (W.Q.Rl.MY 0) hθ
      ((iotaX W.S.X W.Q.instEq).symm (y, 1))
      ((hRS.2.1 _).2 (congrArg Prod.snd ((iotaX W.S.X W.Q.instEq).apply_symm_apply (y, 1))))
    exact ⟨σ, fun T hT x => hσ (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) T hT x⟩
  choose σ hσ using hσ
  have hpt : ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ v (y : W.S.X.B.I.Ginf),
      (fun g => evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v)
        (iotaX W.S.X W.Q.instEq g * (y, W.S.X.xu u))) =
      rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T (σ y v)) := by
    intro T hT v y
    funext g
    rw [hσ y T hT v]
    simp only [evS, rTrans]
    exact congrArg (T v) (shift_swap (iotaX W.S.X W.Q.instEq).toMulEquiv g _ y (W.S.X.xu u) hf1)
  obtain ⟨φL, hφL, rfl⟩ := hb
  obtain ⟨φL', hφL', rfl⟩ := hb'
  rw [hc C _ φL (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T hT v).1 hφL,
    hc C' _ φL' (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T' hT' v).1 hφL']
  refine comb_integral _ c α α' _ _ fun y => ?_
  refine Eq.trans ?_ (hrelAll (W.S.X.Wu u y) (σ y v))
  exact congrArg₂ (fun p q => α * p + α' * q) (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T hT v y))
    (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T' hT' v y))
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwoStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.botRel_of_botHyp_of_pin_central : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u), d.Pin z → _root_.GlobalTheory.MiTop.BottomRelation W z d := by
  first | exact @_root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center | exact _root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center | (intros; apply _root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairs
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem anchor_pairs_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hPu z hzf hzc v hv u
  obtain ⟨-, hInf, -, hMatch, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hEv := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (z * (show GA D (D.sp.Y 0) from W.Q.tS)) v (by simp) hInf hB.gap hB.idE (hMatch z hzf hzc) hv
  obtain ⟨⟨j, hjbij, hj⟩, -⟩ := hEv
  have hF := hB.fin
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  have hpair : ∀ (Tm : MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)) (C : Cu W.S.X u W.S.Y.hK),
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) C
        ⟪((j Tm : HHX W.S.X) : L2X W.S.X), PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C⟫_ℂ := by
    intro Tm C
    unfold _root_.GlobalTheory.MiTop.IsPairing'
    let g : L2X W.S.X := ((j Tm : HHX W.S.X) : L2X W.S.X)
    have hg : (g : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] fun x => star (evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) x) := hj Tm
    refine ⟨star g, ?_, ?_⟩
    · have h1 : ((star g : L2X W.S.X) : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] star (g : W.S.X.B.I.GA → ℂ) := MeasureTheory.Lp.coeFn_star g
      refine h1.trans ((hg.fun_comp star).trans (Filter.EventuallyEq.of_eq ?_))
      funext x
      exact star_star _
    · rw [star_star]
  refine ⟨fun φ => ?_, fun T hT C => ⟨_, hpair ⟨T, hT⟩ C⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (W.S.bij u).2 (D.eMu u φ).1 (hram (D.eMu u φ).2)
    exact ⟨C, hC⟩
  · obtain ⟨φr, hφr⟩ := hPu u
    let x := (D.s_Cu u).symm ⟨φr.1, φr.2.1⟩
    let C : Cu W.S.X u W.S.Y.hK := (W.S.hI hF).eCu u x
    have hpin := W.S.colPin hF u x
    have hC : _root_.GlobalTheory.MiTop.IsColumnForm W u C ((D.eMu u).symm φr) := by
      show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK C = _
      rw [LinearEquiv.apply_symm_apply, ← Formalism.L2.SG.ColDict.colDict_apply W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)]
      have hpin' : Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u) C = D.s_Cu u x := hpin
      rw [hpin', LinearEquiv.apply_symm_apply]
    let P : HHX W.S.X := (Formalism.L2.SG.PackageTie2.sOf hF).Pu u C
    have hP : P ≠ 0 := by
      have e := (W.S.hI hF).Pu_eq u x
      intro h0
      apply hφr
      have : (W.S.hI hF).eHH (D.s.Pu u x) = 0 := e.trans h0
      exact (LinearIsometryEquiv.map_eq_zero_iff _).1 this
    obtain ⟨Tm, hTm⟩ := hjbij.2 P
    refine ⟨(D.eMu u).symm φr, C, _, Tm.1, Tm.2, hC, hpair Tm C, ?_⟩
    rw [hTm]
    have hPv : ((P : HHX W.S.X) : L2X W.S.X) = PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C := rfl
    rw [hPv]
    refine inner_self_ne_zero.2 ?_
    rw [← hPv]
    exact fun h => hP (Subtype.ext h)
end GlobalTheory.MiTop
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairsStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_vector_central_twist_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  first | exact @_root_.GlobalTheory.MiTop.anchor_pairs_alt | exact _root_.GlobalTheory.MiTop.anchor_pairs_alt | (intros; apply _root_.GlobalTheory.MiTop.anchor_pairs_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColCrdHolds
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem colC_eq_lin_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) :
    _root_.GlobalTheory.MiTop.columnOfCoordinates W u = Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1))) := by
  funext x
  exact (Fintype.linearCombination_apply ℂ _ x).symm
theorem colCrd_of_real_pack : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.ColumnCoordinateCondition W := by
  intro D L hT Gi Gl Kc Yd cX ex W u
  have hbij : Function.Bijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) :=
    GlobalTheory.Mem.SJ.lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (W.P.I.eNu u) (D.jN_basis u)
  have hrat : ∀ x, _root_.GlobalTheory.MiTop.columnOfCoordinates W u (cpt D.what₂.embLL x) = D.jN u (W.P.I.eNu u x) := fun x => by
    rw [_root_.GlobalTheory.MiTop.colC_eq_lin_alt]
    exact GlobalTheory.Mem.SJ.lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (W.P.I.eNu u).toLinearMap) x
  refine ⟨_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u ▸ hbij, hrat, 1, one_pos, fun x => ?_⟩
  rw [one_mul]
  let e : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
    LinearEquiv.ofBijective (Formalism.IndefR.Cx.lin (fun k => D.jN u (W.P.I.eNu u (Pi.single k 1)))) hbij
  have hv0 : W.P.A3.A.v0 = InfinitePlace.mk D.what₂.embLL := W.Q.Rl.hv0
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a =
      Formalism.IndefR.Links.cj (Formalism.L2.SG.JoinSI.twQ W.P) (D.what₂.embLL a) := by
    intro a
    rw [← hv0]
    exact _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL W.Q a
  have key := GlobalTheory.Mem.SJ.fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL (Formalism.L2.SG.JoinSI.twQ W.P) htw
    (GlobalTheory.Mem.SJ.colNorm_exists_im_ne_zero _) (D.div.Nu u) _ (W.P.NuC (W.P.I.wU u)) _ (W.P.I.eNu u)
    (W.P.tied.div.cols.Nu u) (D.what₂.Mu u) (D.jN u) e.symm (GlobalTheory.Mem.SJ.colNorm_normAt_column D u)
    (fun y => by
      rw [LinearEquiv.symm_symm]
      exact (congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) _).symm.trans (hrat y)) (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x)
  have hx : e.symm (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x) = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact congrFun (_root_.GlobalTheory.MiTop.colC_eq_lin_alt W u) x
  rw [hx] at key
  have hv : W.P.A3.fam3.base3.v0 = InfinitePlace.mk D.what₂.embLL := hv0
  rw [hv]
  exact key
end GlobalTheory.MiTop
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PostOnMemEEatOfCenter
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
set_option maxHeartbeats 800000
open Formalism.BasicNotions.TH Formalism.IndefR.Lev
namespace GlobalTheory.MiTop.CentralShift
section General
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
end General
section Main
open GlobalTheory.MiTop.CentralShift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem postOn_rTrL_mem_EEat_of_mem_center (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z : GA D (Yc D 0)} (hzf : z ∈ GfC (Yc D 0))
    (hzc : z ∈ Subgroup.center (GA D (Yc D 0))) (Pl : LevelP W.Q.Rl.toRealDat.Pg D.R.r ℂ) {T : MMap (W.Q.Rl.MY 0)}
    (hT : T ∈ W.Q.Rl.toRealDat.EEat Pl) :
    postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) T ∈ W.Q.Rl.toRealDat.EEat Pl := by
  unfold RealDat.EEat at hT ⊢
  refine GlobalTheory.MultTranslate.postOn_mem_goodPart hzf (fun k hk => ?_) (fun f => ?_) hT
  · have e : z⁻¹ * k * z = k := by
      rw [mul_assoc, Subgroup.mem_center_iff.mp hzc k, inv_mul_cancel_left]
    rw [e]
    exact ⟨hk, rfl⟩
  · unfold RealDat.e0
    exact gaL_rTr_of_center _ _ _ _ hzc f
end Main
end GlobalTheory.MiTop.CentralShift
namespace GlobalTheory.MiTop
open GlobalTheory.MiTop.CentralShift
theorem exists_isShift_of_center_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∃ V, _root_.GlobalTheory.MiTop.IsShiftOperator W z V := by
  intro D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc
  have hM := hB.hyp.2.2.2.1.models
  have hE := hM.HE
  have h0 := hM.ν0
  have hHaar : W.Q.Rl.ν0.IsHaarMeasure := h0.1.1
  have hFD := h0.2
  obtain ⟨hinj, hrange, hip⟩ := hE
  have he : ∀ e, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat W.Q.Rl.toRealDat.triv := fun e => by
    rw [← hrange]; exact LinearMap.mem_range_self _ e
  have hmem : ∀ e, postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) ∈ LinearMap.range W.Q.Rl.HE.e :=
    fun e => by rw [hrange]; exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e)
  let Lr : W.Q.Rl.HE.H →ₗ[ℂ] LinearMap.range W.Q.Rl.HE.e :=
    (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) ∘ₗ W.Q.Rl.HE.e).codRestrict _ hmem
  let Vz : W.Q.Rl.HE.H →ₗ[ℂ] W.Q.Rl.HE.H := (LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm.toLinearMap ∘ₗ Lr
  have hV : ∀ e, W.Q.Rl.HE.e (Vz e) = postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e) := by
    intro e
    have h1 : ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) : LinearMap.range W.Q.Rl.HE.e) : MMap (W.Q.Rl.MY 0)) =
        W.Q.Rl.HE.e ((LinearEquiv.ofInjective W.Q.Rl.HE.e hinj).symm (Lr e)) := LinearEquiv.ofInjective_apply _ _
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hzc' : z⁻¹ ∈ Subgroup.center (GA D (Yc D 0)) := Subgroup.inv_mem _ hzc
  have hipv : ∀ e e' : W.Q.Rl.HE.H,
      ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (W.Q.Rl.HE.e e) (W.Q.Rl.HE.e e') =
        ipM (W.Q.Rl.MY 0) W.Q.Rl.ν0 W.Q.Rl.fd0 (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e))
          (postOn (W.Q.Rl.MY 0) (GlobalTheory.FinTranslate.rTrL (Yc D 0) z) (W.Q.Rl.HE.e e')) := by
    intro e e'
    have m1 := (Submodule.mem_inf.mp (he e)).1
    have m2 := (Submodule.mem_inf.mp (he e')).1
    have m3 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e))).1
    have m4 := (Submodule.mem_inf.mp (_root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ (he e'))).1
    apply ipM_eq_of_iff
    intro c
    constructor
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z 1 (by simp) (map_mul_right_center _ hHaar hzc)
        _ m1 _ m2 _ _ (fun v g => by rw [one_mul]; rfl) (fun v g => by rw [one_mul]; rfl) c
    · exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift _ _ _ _ _ _ hHaar hFD z⁻¹ 1 (by simp) (map_mul_right_center _ hHaar hzc')
        _ m3 _ m4 _ _ (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e v) (inv_mul_cancel_right g _).symm)
        (fun v g => by rw [one_mul]; exact congrArg (W.Q.Rl.HE.e e' v) (inv_mul_cancel_right g _).symm) c
  refine ⟨Vz, fun e v => ?_, fun e => ?_, fun e hel => ?_⟩
  · unfold _root_.GlobalTheory.MiTop.rowFormOfVector
    rw [hV]
    exact lift_postOn _ _ _
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hip, hip, hV, ← hipv]
  · rw [hV]
    exact _root_.GlobalTheory.MiTop.CentralShift.postOn_rTrL_mem_EEat_of_mem_center W hzf hzc _ hel
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2AtRealisation
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.AtReal
open Formalism.IndefR.Links
section Gen
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}
end Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem dc_heq_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : HEq (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc W.P.Dc :=
  (congr_arg_heq W.Dcf W.Q.zs).trans (heq_of_eq W.Q.dc)
theorem df1_fc_eq_side3 (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1 = W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs :=
  congrArg (W.P.A3.side3 W.P.Ps W.P.ψs) W.Q.zs
theorem exists_word_heq_of_mem_dc (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem) : ∃ u, HEq m (W.P.I.wU u) := by
  obtain ⟨m', hm⟩ := cols_mem (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W) (_root_.GlobalTheory.MiTop.AtReal.dc_heq_alt W) m
  refine ⟨W.Q.wdD m', ?_⟩
  rw [W.Q.wU_wdD]; exact hm
end GlobalTheory.MiTop.AtReal
namespace GlobalTheory.MiTop.AtReal
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem anchor_word_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (u : D.what₂.Word) (d : _root_.GlobalTheory.MiTop.BottomData W u) (v : (W.Q.Rl.MY 0).Vec)
    (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ) (hR : _root_.GlobalTheory.MiTop.BottomRelation W z d)
    (hA : (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0)
    (hr : 0 < r) (hU : ∀ φ, ‖U φ‖ = r * ‖φ‖) (hRel : d.Rel U c)
    (hrow : ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.MiTop.rowFormOfTuple W t F ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W) :
    ∃ (R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (p b₀ : ℂ), p ≠ 0 ∧ b₀ ≠ 0 ∧
      ∀ t (φ : D.what₂.Mu u) (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
        (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ C b, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R (U φ)) →
        _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F' (PiTensorProduct.tprod ℂ v)) C b →
        c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) * b₀ = p * b := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨-, -, φ₁, C₀, b₀, T₀, hT₀, hC₀, hP₀, hb₀⟩ := hA
  have hinj : Function.Injective U := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ h
    have h1 := hU φ
    rw [h, norm_zero] at h1
    exact norm_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_left hr.ne')
  obtain ⟨φ₀, hφ₀⟩ := LinearMap.injective_iff_surjective.1 hinj (R.symm φ₁)
  have hC₁ : _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ (R (U φ₀)) := by rw [hφ₀, LinearIsometryEquiv.apply_symm_apply]; exact hC₀
  obtain ⟨p, hp⟩ := hRel T₀ hT₀
  refine ⟨R, p φ₀, b₀, fun h0 => hb₀ ?_, hb₀, fun t φ F F' hF C b hC hb => ?_⟩
  · obtain ⟨F, hF⟩ := heq_fin' (α := D.what₂.LL)
      (congrArg (fun Df => DefSide.nV Df W.P.A3.A.μ0) (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W)).symm (fun _ => 0)
    have h1 := hp φ₀ φ₀ W.P.A3.A.μ0 F _ hF 1 0 (by rw [h0, mul_zero, zero_mul, add_zero])
    have h2 := hR (U φ₀) (U φ₀) T₀ hT₀ T₀ hT₀ 1 0
      (fun y w => by have h3 := h1 y w; rw [zero_mul] at h3 ⊢; exact h3) _ C₀ C₀ b₀ b₀ hC₁ hC₁ hP₀ hP₀
    rwa [one_mul, zero_mul, add_zero] at h2
  · have h1 := hp φ₀ φ t F F' hF
      (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) (-p φ₀) (by ring)
    have h2 := hR (U φ₀) (U φ) T₀ hT₀ _ (hrow t F') _ _ h1 _ C₀ C b₀ b hC₁ hC hP₀ hb
    linear_combination h2
end GlobalTheory.MiTop.AtReal
namespace GlobalTheory.MiTop
open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal
set_option maxHeartbeats 1000000 in
theorem miStar2_at_realisation_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) → _root_.GlobalTheory.MiTop.JointCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hΘ hJ hPu
  classical
  obtain ⟨z, hzf, hzc, hw⟩ := hJ
  choose d U r c hpin hr hUn hUC hRel using hw
  obtain ⟨V₀, hV₀⟩ := _root_.GlobalTheory.MiTop.exists_isShift_of_center_alt W hB z hzf hzc
  have hMt := _root_.GlobalTheory.MiTop.botHyp_match_alt W hB
  have hS : parB (Ptw D) (min 0 D.R.m) = parB (Ptw D) 0 := by simp
  obtain ⟨v, hv⟩ := GlobalTheory.Core.Mi.exists_conjVec hDS D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) hS hMt.2.1 hB.gap hB.idE
  obtain ⟨κ, hκ, hPF⟩ := _root_.GlobalTheory.T.pairForm_of_conjVec_of_botHyp hDS hCR W hB v hv
  have hCC := _root_.GlobalTheory.MiTop.colCrd_of_real_pack W
  have hrow : ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.MiTop.rowFormOfTuple W t F ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W :=
    fun t F => hMt.2.2.2.2.2 _ (hΘ t F)
  have hanc := fun u => _root_.GlobalTheory.T.conjugate_vector_central_twist_alt hDS hCR W hB hPu z hzf hzc v hv u
  have hword := fun u => _root_.GlobalTheory.MiTop.AtReal.anchor_word_alt W z u (d u) v (U u) (r u) (c u)
    (_root_.GlobalTheory.T.botRel_of_botHyp_of_pin_central hDS hCR W hB z hzf hzc u (d u) (hpin u)) (hanc u) (hr u) (hUn u) (hRel u) hrow
  choose R p b₀ hp hb₀ hid using hword
  have key : ∀ m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem, ∃ (Um : Matrix (Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m)) (Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m)) ℂ) (cm : W.P.A3.fam3.base3.Tup → ℂ),
      (∀ x, fnorm ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) (Um.mulVec x) = fnorm ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) x) ∧
      (∀ t, cm t ≠ 0) ∧ (∀ w (k : D.what₂.LL), W.P.A3.fam3.base3.v0.embedding k = cm ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).μ w) / cm W.P.A3.fam3.base3.μ0 → vw w k = 0) ∧
      ∃ pp bb : ℂ, pp ≠ 0 ∧ bb ≠ 0 ∧ ∀ t (φ : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m) → D.what₂.LL) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
        cm t * W.P.A3.fam3.base3.v0.embedding ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Pt m t φ F) * bb =
          pp * ⟪W.Q.sEE (Tw.map (Formalism.L2.SG.JoinSI.twQ W.P) V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))), (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Sp.Pu m (Um.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))⟫_ℂ := by
    intro m
    obtain ⟨u, hm⟩ := _root_.GlobalTheory.MiTop.AtReal.exists_word_heq_of_mem_dc W m
    obtain ⟨ha, hXc, hPt⟩ := cols_heq (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W) (_root_.GlobalTheory.MiTop.AtReal.dc_heq_alt W) hm
    obtain ⟨hbij, hrat, r', hr', hnorm⟩ := hCC u
    let s := Formalism.L2.SG.JoinSI.twQ W.P
    let cL : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] D.what₂.Mu u :=
      { toFun := _root_.GlobalTheory.MiTop.columnOfCoordinates W u
        map_add' := fun x y => by simp only [_root_.GlobalTheory.MiTop.columnOfCoordinates, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a x => by simp only [_root_.GlobalTheory.MiTop.columnOfCoordinates, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    let eC : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u := LinearEquiv.ofBijective cL hbij
    have heC : ∀ x, eC x = _root_.GlobalTheory.MiTop.columnOfCoordinates W u x := fun x => rfl
    let A : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := ((r u : ℂ))⁻¹ • (((R u).toLinearEquiv : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) ∘ₗ U u)
    have hAap : ∀ φ, A φ = R u (U u (((r u : ℂ))⁻¹ • φ)) := fun φ => by
      show ((r u : ℂ))⁻¹ • R u (U u φ) = _
      rw [map_smul, map_smul]
    have hA : ∀ φ, ‖A φ‖ = ‖φ‖ := fun φ => by
      show ‖((r u : ℂ))⁻¹ • R u (U u φ)‖ = ‖φ‖
      rw [norm_smul, LinearIsometryEquiv.norm_map, hUn u, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr u).le,
        ← mul_assoc, inv_mul_cancel₀ (hr u).ne', one_mul]
    let f' : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) :=
      { toFun := fun y => Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s y))))
        map_add' := fun x y => by simp only [Formalism.L2.SG.JoinSI.cjv_add, map_add (f := _)]
        map_smul' := fun a x => by
          simp only [Formalism.L2.SG.JoinSI.cjv_smul, map_smul, Formalism.IndefR.Links.cj_cj, RingHom.id_apply] }
    obtain ⟨M, hM⟩ := heq_mat ha (LinearMap.toMatrix' f')
    have hcj : ∀ a : D.what₂.LL, W.P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj s (D.what₂.embLL a) :=
      _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL W.Q
    have hr0 : ((r u : ℂ))⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (hr u).ne')
    refine ⟨M, fun t => Formalism.IndefR.Links.cj s (c u t), ?_, fun t => (map_ne_zero _).2 ((hUC u).1 t), ?_,
      Formalism.IndefR.Links.cj s (p u), Formalism.IndefR.Links.cj s (κ * ((r u : ℂ))⁻¹ * b₀ u), (map_ne_zero _).2 (hp u),
      (map_ne_zero _).2 (mul_ne_zero (mul_ne_zero hκ hr0) (hb₀ u)), ?_⟩
    · intro x
      obtain ⟨x', hx⟩ := heq_fin ha x
      rw [heq_fnorm ha (hXc _) (heq_mulVec ha hM hx), heq_fnorm ha (hXc _) hx, LinearMap.toMatrix'_mulVec]
      show fnorm _ (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s x'))))) = _
      conv_rhs => rw [← Formalism.L2.SG.JoinSI.cjv_cjv s x']
      rw [hnorm, hnorm, ← heC, ← heC, LinearEquiv.apply_symm_apply, hA]
    · intro w k hk
      apply (hUC u).2 w k
      rw [hcj, ← map_div₀] at hk
      exact (Formalism.IndefR.Links.cj s).injective hk
    · intro t φ F
      obtain ⟨φ', hφ⟩ := heq_fin ha φ
      have hnV : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t = (W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t :=
        congrArg (fun Df => DefSide.nV Df t) (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W)
      obtain ⟨F'', hF⟩ := heq_fin hnV F
      rw [hPt t φ φ' F F'' hφ hF, hcj, hB.hyp.2.2.1 u t (hB.used t) φ' F'']
      set ψ := D.jN u (W.P.I.eNu u φ') with hψ
      have hvec : HEq (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ)) (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A ψ))) := by
        refine (heq_mulVec ha hM (heq_cpt _ ha hφ)).trans (heq_of_eq ?_)
        rw [LinearMap.toMatrix'_mulVec]
        show Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ'))))) = _
        have e1 : Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ') = cpt D.what₂.embLL φ' := by
          funext i
          show Formalism.IndefR.Links.cj s (W.P.A3.fam3.base3.v0.embedding (φ' i)) = D.what₂.embLL (φ' i)
          rw [hcj, Formalism.IndefR.Links.cj_cj]
        rw [e1, heC, hrat]
      have hx' : HEq (eC.symm (A ψ)) (Formalism.L2.SG.JoinSI.cjv s (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))) := by
        have h2 := heq_cjv s ha hvec
        rw [Formalism.L2.SG.JoinSI.cjv_cjv] at h2
        exact h2.symm
      rw [← Formalism.L2.SG.JoinSI.cjv_cjv s (M.mulVec _)]
      obtain ⟨T, hTc⟩ := (hanc u).1 (_root_.GlobalTheory.MiTop.columnOfCoordinates W u (eC.symm (A ψ)))
      obtain ⟨b, hb⟩ := (hanc u).2.1 (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F) (hrow t F) T
      have hE := (hV₀.2.2 _ (hΘ t F))
      have hPair : _root_.GlobalTheory.MiTop.IsPairing' W u (show GA D (D.sp.Y 0) from W.Q.tS)
          (_root_.GlobalTheory.MiTop.rowFormOfVector W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))))) (PiTensorProduct.tprod ℂ v)) T b := by
        obtain ⟨φL, hφL, hbL⟩ := hb
        refine ⟨φL, hφL.trans (Filter.EventuallyEq.of_eq ?_), hbL⟩
        funext x
        refine Eq.trans ?_ (congrFun (hV₀.1 (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))) (PiTensorProduct.tprod ℂ v))
          ((iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS))).symm
        refine congrArg (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F (PiTensorProduct.tprod ℂ v)) ?_
        show (iotaX W.S.X W.Q.instEq).symm x * (z * (show GA D (D.sp.Y 0) from W.Q.tS)) =
          (iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS) * z
        rw [mul_assoc, Subgroup.mem_center_iff.1 hzc]
      have hpair := hPF (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))))
        hE u m hm _ _ hx' T b hTc hPair
      refine Eq.trans ?_ (congrArg (fun a => Formalism.IndefR.Links.cj s (p u) * a) hpair.symm)
      show Formalism.IndefR.Links.cj s (c u t) * _ * _ = Formalism.IndefR.Links.cj s (p u) * Formalism.IndefR.Links.cj s (κ * b)
      have hcolR : _root_.GlobalTheory.MiTop.IsColumnForm W u T (R u (U u (((r u : ℂ))⁻¹ • ψ))) := by
        rw [← hAap]; unfold _root_.GlobalTheory.MiTop.IsColumnForm at hTc ⊢; rw [hTc, ← heC, LinearEquiv.apply_symm_apply]
      have hid' := hid u t (((r u : ℂ))⁻¹ • ψ) F'' F hF.symm T b hcolR hb
      rw [GlobalTheory.ExpAtTypePrimes.perCol_smul] at hid'
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      linear_combination κ * hid'
  choose Um cm hUm hc0 hcU hAn using key
  exact GlobalTheory.MiTop.miStar2_of_anchored (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) (Formalism.L2.SG.JoinSI.twQ W.P) V₀) Um cm
    ⟨fun e he => ⟨hV₀.2.2 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) he, hV₀.2.1 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e)⟩, hUm⟩ hAn ⟨hc0, hcU⟩
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2AtRealisationStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_star_product_nonvanishing_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) → _root_.GlobalTheory.MiTop.JointCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  first | exact @_root_.GlobalTheory.MiTop.miStar2_at_realisation_alt | exact _root_.GlobalTheory.MiTop.miStar2_at_realisation_alt | (intros; apply _root_.GlobalTheory.MiTop.miStar2_at_realisation_alt <;> assumption)
end
end
