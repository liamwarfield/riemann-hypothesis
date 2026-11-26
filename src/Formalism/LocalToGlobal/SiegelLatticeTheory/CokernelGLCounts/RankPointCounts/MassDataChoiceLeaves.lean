module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataVolumesS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepChoiceDataC_of_leavesG
    (hSW : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
      Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
        Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, -, -, s₀, t₀, hS⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨max s₀ 29, max t₀ 16, fun C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ hT => ?_⟩
  obtain ⟨-, -, hrd, -, hg, -⟩ := hS C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc
  have hGap : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h2) (le_trans (le_max_right _ _) h1)
  have e := fun {P} (h : OnTied P) => h Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT
  exact ⟨0, 0, 1, X.Fu u, Y.what₂ u, fun _ => 0, pairSys0 u u' (X.Fu u) (Y.what₂ u), fun _ => idx0 D,
    fun _ => idx0 D, fun _ => 0,
    massDataValid_bk_of X hb Y u u' X0 ψ 0 0 1 (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D)
      (fun _ => idx0 D) (fun _ => 0) hc hrd (by linarith) hT (level_s_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inMassesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inColumnsAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inIndicesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (volumes_s_at_instance hSW X hb Y.hK _ _ u u' X0 _ _) (kpp_volume_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (e hTy) (e hPC) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
      (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim) (Formalism.L2.SG.LocVolKap.kapX X hb u u')
      (Formalism.L2.SG.Pf.realObj_inNuX X u u' 1) (hInfG D X u u' hGap) (e hPos) (e hFV)⟩

theorem choice_massData (hSW : PI.VolStabS.MassDataS.SWXS)
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1) :
    StepChoiceConstantsC := by
  exact stepChoiceDataC_of_leavesG hSW MassDataX.nTy_holds hPC hInfG (MassDataX.nPos_of hSW hPC) (MassDataX.frameVolAt_of_prodConv hPC)

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolOrb
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.ZsVolCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StabInCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ CZ M δ u u' (ZhatL (lf D F0) F') L

def OrbActE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∃ (X : Type) (_ : MulAction (CZ M δ u u' (ZhatL (lf D F0) F') L) X) (x : X),
      MulAction.stabilizer (CZ M δ u u' (ZhatL (lf D F0) F') L) x =
        (PairVal.stabAut D u u' F0 what₂ γ F' L).subgroupOf (CZ M δ u u' (ZhatL (lf D F0) F') L) ∧
      Nonempty (MulAction.orbit (CZ M δ u u' (ZhatL (lf D F0) F') L) x ≃
        PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F'))

def OrbFinE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Finite

theorem orbStabE_of (h1 : StabInCZ M δ u u' F0 what₂) (h2 : OrbActE M δ u u' F0 what₂) (h3 : OrbFinE M δ u u' F0 what₂) :
    OrbStabE M δ u u' F0 what₂ (CZ M δ u u') := by
  intro γ w F' L U hH
  obtain ⟨X, inst, x, hstab, ⟨e⟩⟩ := h2 γ w F' L U hH
  have hidx : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (CZ M δ u u' (ZhatL (lf D F0) F') L) =
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  refine ⟨h1 γ w F' L U hH, hidx, ?_⟩
  have hne : (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Nonempty :=
    ⟨(e ⟨x, MulAction.mem_orbit_self x⟩).1, (e ⟨x, MulAction.mem_orbit_self x⟩).2⟩
  exact ((Set.ncard_pos (h3 γ w F' L U hH)).2 hne).ne'

end Formalism.L2.SG.Pf.ZsVolOrb

end
end
