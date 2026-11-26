module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsGoodCoverAtMinimalLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Fc.RL
open GlobalTheory.Fc
variable (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition)
def Row_tie_alt : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.HasCompatibility)
open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting _root_.Formalism.L2.SG.RowDict _root_.Formalism.L2.SG.PoincareInHH.PoincareSetting _root_.Formalism.L2.SG.PackageTie2 in
def RowLabelCondition : Prop := Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
  AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι)
def RowGoodnessCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D)
def RowGeometricCondition (CF : ℝ) : Prop := Row Q Lk (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∃ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt ∧
  GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF)
def RowMultiplicityCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b =>
  (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)
def RowKappaCondition : Prop := Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P)
def RowDefectCondition : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def LinkedAt (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (r : V4.Slot → LkT _root_.GlobalTheory.Fc.BundleCondition → Prop) : Prop :=
  Lg1 KPx (IsBuiltE p.s) (IsGoodE p.s) fun S => r S (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
theorem LinkedAt.of_row {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop} (h : Row (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) H) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L H :=
  ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, h.strengthen fun _ _ _ _ _ t => t.1⟩
end GlobalTheory.Fc.RL
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundle
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundle
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.MemberCount
theorem rankMu_of_bundle_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (u : D.what₂.Word) :
    GlobalTheory.Core.Rk.RankMu D u :=
  rankMu_of_cols D O.ex.lev b.R.T.toTiedDataS.cols O.ex.duStar_def u
theorem rankMu_of_good_linked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  fun _ _ => RowE.of_all fun _ _ _ _ b _ _ _ u => _root_.GlobalTheory.Fam.MemberCount.rankMu_of_bundle_alt b u
end GlobalTheory.Fam.MemberCount
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundleStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankMu_all_linked_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | exact _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked | (intros; apply _root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEV0EqICPq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEV0EqICPq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
open _root_.Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 1000000 in
theorem theta_eV0_eq_iC_Pq_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEV0EqICPqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq_alt | exact _root_.GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.theta_eV0_eq_iC_Pq_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackB
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackB
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.BundleLev
theorem lev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = x.R.Pg ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xiH t = x.R.toLevCh.xiH (x.Y.tupT ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      k.B.Q.Rl.toRealDat.Pg = x.R.Pg ∧ ∀ t, k.B.Q.Rl.toRealDat.xiH t = x.R.toLevCh.xiH (x.Y.tupT (k.P.I.tup t)) := by
    intro k hk
    subst hk
    refine ⟨rfl, fun t => ?_⟩
    exact (congrArg x.R.toLevCh.xiH (x.Y.tupT_tup t)).symm
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq
set_option maxHeartbeats 1000000 in
theorem pg_eq_vGs_and_xiH_eq_xi_of_twArgs {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) :
    x.R.Pg = (q.B.primes q.w.px).vGs ∧
      ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → x.R.toLevCh.xiH (x.Y.tupT μ) = q.w.I.xi μ := by
  have h := GlobalTheory.Mem.R3.twArgs_lev K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have e : a.x = x := eq_of_heq ax
  subst e
  exact ⟨eq_of_heq h.2.1, fun μ hμ => eq_of_heq (h.2.2.1 μ hμ).2⟩
set_option maxHeartbeats 1000000 in
theorem levTrue_packB_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hw
  have h1 := _root_.GlobalTheory.Fam.BundleLev.lev_of_btw_alt b hw.x hw.y
  have h2 := _root_.GlobalTheory.Fam.BundleLev.pg_eq_vGs_and_xiH_eq_xi_of_twArgs q hw.x hw.a hw.ax
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := h1.1.trans h2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hPg]
    exact ColTest.isTypePlaces_vGs q.w.I q.w.l q.Z q.w.ok
  · intro PP
    rw [hPg]
    exact Iff.rfl
  · intro t
    exact (h1.2 t).trans (h2.2 _ (_root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b) t))
end GlobalTheory.Fam.BundleLev
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTruePackBStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fam_levTrue_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) := by
  first | exact @_root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit | exact _root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit | (intros; apply _root_.GlobalTheory.Fam.BundleLev.levTrue_packB_of_bWit <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeries
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseCmp
open GlobalTheory.FlatVecSum (princ princ_good)
section Real
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle}
  {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ}
end Real
section Coef
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}
end Coef
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
end Move
section Read
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {X : Type} (rd : M →ₛₗ[eK] (X → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end Read
end GlobalTheory.BaseCmp
namespace GlobalTheory.BigOn.Exp
open Formalism.MainNotions.DIV.Cons _root_.Formalism.L2.Indef _root_.Formalism.L2.Indef.Tree Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.BaseCmp
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem core_of_rows_alt (hr : p.PointConditions') : GlobalTheory.Hk3.Core p.R.toRealDat p.F.lv2 :=
  have hc := RealDat3.characterisation_of_weak p.charW hr.exAt
  ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
theorem exists_series_alt (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) (O' : Subring ℂ) (hO' : ∀ a : 𝓞 D.what₂.LL, D.what₂.embLL a ∈ O') {ω φ}
    (hk : IsKernel p.R.toRealDat j (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w)))
      (GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w))) ω φ) {x}
    (hx : x ∈ seriesSet p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 ω φ) :
    ∃ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) (ζ : ℂ) (n : ℕ),
      IsIntegral ℤ (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * ζ) ∧
      P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q} ∧
      ν⁻¹ • adForm p.R.toRealDat j x (p.v₀ j _) = ζ • ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
  classical
  have hC := _root_.GlobalTheory.BigOn.Exp.core_of_rows_alt hr
  have hp := hf.pin
  set i := ex.nch.twI w with hi
  set b := ex.nch.sd w with hb
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hρ hp i j b
  have hl : D.ntw.l i = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := (ex.nch.twI_l w).trans (GlobalTheory.Mem.Top.Bl.resChar_eq_plc D w)
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq, hl]
    rfl
  have hQ : GlobalTheory.OnTies.placesOver p.R.toRealDat (p.R.mu (D.plEq w)) (ownAt D (D.plEq w)) = (ρ.B i j b).de.Q :=
    Finset.ext fun P => by
      rw [(placesAt hw hρ hp).1 P, GlobalTheory.OnTies.placesOver, Finset.mem_filter, hpD]
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D _ _ _ _ _ p.R.toRealDat _ hC j _ hw p.charW.tup.mu_on ω φ hk
  rw [hQ] at hK
  have hN : ownAt D (D.plEq w) ≠ 0 := by
    unfold ownAt
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  obtain ⟨k, hkf, c, m, hc, H⟩ := exists_trace_eq hC p.qGuard (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)) hB hBo hK
    (hl ▸ hp.delta i j b) ⟨_, fun P h => (((placesAt hw hρ hp).1 P).1 h).1⟩ hN
    (fun P h => (hpD P).1 (((placesAt hw hρ hp).1 P).1 h).2) p.P.P0 p.P.ψ0⁻¹ ((p.R.eG.trans p.cG).trans (ρ.eG i j b))
    (fun g P h h' a c => by
      have e := hp.grp i j b (p.cG (p.R.eG g)) P h h' a c
      rw [MulEquiv.symm_apply_apply] at e
      exact e)
    (mem_level_iff hm hf.level i j b)
    (fun u hu => by
      refine (level_chi hm hρ hf.level i j b u hu).1.trans ?_
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀])
    (hρ.weil_base i j b)
  obtain ⟨h, hh, y, hy, hx⟩ := hx
  obtain ⟨hy', hs⟩ := H h y hy
  obtain ⟨hν, c₀, ⟨gramR, c0R, c0L, hT, u, hu, hsc⟩, n₀, hn₀, hpow⟩ := hf.norm
  rw [p.phsOne, map_one, one_mul] at hpow
  have hc₀ : c₀ ≠ 0 := fun h0 => hν (pow_eq_zero_iff hn₀ |>.1 (by rw [hpow, h0, zero_pow hn₀]))
  obtain ⟨cc, hcc, hbij, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ hC ⟨p.fw⟩ j _ _
    (p.O j) (p.pins j).2
  obtain ⟨-, -, hval, -⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ _ p.T p.R.toRealDat _ p.κ p.v₀ p.O hC ⟨p.fw⟩ hr.ioExt j
    (p.pins j) cc hcc u hu _ hB hBo
  have hmem := mem_span_coefLat hC hBo ⟨gramR, c0R, hT⟩ (p.R.ioP j (PiTensorProduct.tprod ℂ u))
    (fun z => by obtain ⟨z, rfl⟩ := hbij.2 z; exact hval z) hc₀ hsc (ρ.eO i b).range O' hO' hy'
  obtain ⟨s, h', T, ζ, hζ, hT1, hT2⟩ := exists_move hρ i j b (mul_mem hh hkf)
  obtain ⟨-, n, hc1, -⟩ := hc
  have hN' : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  refine ⟨s, h', T (c₀⁻¹ • p.R.ioP j (PiTensorProduct.tprod ℂ u) ((((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m) • y)),
    (c₀ / ν) * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹, n + m, ?_, ?_, ?_⟩
  · have h1 : IsIntegral ℤ (c₀ / ν) := isIntegral_of_root ⟨n₀, hn₀, by rw [div_pow, hpow, div_self (pow_ne_zero _ hc₀)]⟩
    rw [show ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (n + m) * (c₀ / ν * c * ζ * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
      c₀ / ν * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ n * c) * ζ by rw [pow_add]; field_simp]
    exact (h1.mul hc1).mul (isIntegral_of_root hζ)
  · have h1 := Submodule.mem_map_of_mem (f := T.restrictScalars O') hmem
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨Q, hQ, rfl⟩
    exact hT2 Q hQ
  · have e : p.v₀ j (sg0 D p.P.A3.A) = fun τ => (u τ : (p.R.MW j (sg0 D p.P.A3.A)).sm τ) := funext fun τ => (hu τ).symm
    rw [e, hx u, one_smul, hs u]
    change ν⁻¹ • c • ρ.theta i j b _ _ = _
    rw [hT1, map_smul, map_smul, map_smul]
    simp only [Setup.theta, map_smul, smul_smul]
    congr 1
    field_simp
theorem realBase_le_baseLat_of_fit_can (hr : p.PointConditions') (hm : RecTies p) (hw : D.plEq w ∈ p.R.twPl) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    (hf : Fit p w j hρ ν) {rd : Can p w j} (hcan : IsCan p rd) : realBase p rd ≤ baseLat p w j hρ ν := by
  obtain ⟨-, e, he1, he2⟩ := hf.adapted
  obtain ⟨Z⟩ := hm.series
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hf.norm.1 hr.prim.unif
    p.charW.base.models.HW (Z.vec j) hK
  have hL : ∀ c : D.ntw.O (ex.nch.twI w), e (algebraMap _ (FractionRing (ex.nch.Oe w)) c) =
      ρ.e (ex.nch.twI w) (ex.nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)),
      IsScalarTower.algebraMap_apply _ (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w), he2, hρ.ek_e]
    rfl
  set Ψ := readExt (rdAt p w j hρ ν) e hL with hΨ
  have hint : ∀ a : 𝓞 D.what₂.LL, ∃ o : ex.nch.Oe w, algebraMap _ (FractionRing (ex.nch.Oe w)) o = ex.nch.embW w a := fun a =>
    exists_of_integral e (N := 1) (n := 0) (by simp) (by
      rw [pow_zero, one_mul, he1]
      exact map_isIntegral_int _ a.isIntegral_coe)
  have hrd : ∀ y, Ψ (rd y) = ν⁻¹ • adForm p.R.toRealDat j y (p.v₀ j _) := fun y => by
    obtain ⟨y, rfl⟩ := (p.nexp.fi j).e.surjective y
    change Ψ (rd ((p.nexp.fi j).e y)) = ν⁻¹ • evW p.nexp p.v₀ j y
    obtain ⟨n, β, hβ, -, -, -, hs⟩ := hK
    have hy : y ∈ Submodule.span D.what₂.LL (Set.range β) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine (congrArg Ψ (hcan ⟨β a, hβ a⟩)).trans ?_
      rw [hΨ, readExt_tmul, map_one, one_smul]
      refine (realRd_tmul p.nexp p.v₀ hρ _ j _ ν _ _).trans ?_
      congr 1
      exact mul_right_eq_self₀.2 (Or.inl (map_one (ρ.e _ _)))
    | zero => rw [map_zero, map_zero, smul_zero]; exact (congrArg Ψ rd.map_zero).trans Ψ.map_zero
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _), smul_add, ← hu, ← hv, ← Ψ.map_add]; exact congrArg Ψ (rd.map_add _ _)
    | smul c u _ hu =>
      rw [map_smul, evW_smul, smul_comm, ← hu, ← he1, hΨ, ← readExt_smul]
      exact congrArg _ (rd.map_smulₛₗ _ _)
  let O' : Subring ℂ := (e.comp (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)))).range
  have hser : ∀ s h, ∀ P ∈ Submodule.span O' {Q | ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q},
      ∃ t ∈ baseLat p w j hρ ν, Ψ t = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := fun s h P hP => by
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, e1⟩ := hf.rat.1 s h Q hQ
      refine ⟨_, Submodule.subset_span ⟨f, ⟨s, h, Q, hQ, e1⟩, rfl⟩, ?_⟩
      rw [← e1, hΨ]
      exact (readExt_tmul _ e hL 1 f).trans (by rw [map_one, one_smul])
    | zero => exact ⟨0, zero_mem _, Ψ.map_zero.trans (LinearMap.map_zero _).symm⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨t', m2, e2⟩ := h2
      exact ⟨t + t', add_mem m1 m2, by rw [Ψ.map_add, e1, e2]; exact (LinearMap.map_add _ _ _).symm⟩
    | smul a Q _ h1 =>
      obtain ⟨t, m1, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := a
      refine ⟨o • t, Submodule.smul_mem _ o m1, ?_⟩
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o t, hΨ, readExt_smul, ← hΨ, e1]
      exact (LinearMap.map_smul _ _ _).symm
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ thetaBase p.R.toRealDat j p.P.P0 p.P.ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) at hx
  change rd x ∈ baseLat p w j hρ ν
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, φ, hk, hx⟩ := hx
    obtain ⟨s, h, P, ζ, n, hζ, hP, e1⟩ := _root_.GlobalTheory.BigOn.Exp.exists_series_alt hr hm hw hf O'
      (fun a => by obtain ⟨o, ho⟩ := hint a; exact ⟨o, by rw [RingHom.comp_apply, ho, he1]⟩) hk hx
    obtain ⟨t, ht, e2⟩ := hser s h P hP
    rcases exists_scalar_of_readExt _ e hL hF (x := rd x) (t := t) (ζ := ζ) (((hrd x).trans e1).trans (congrArg _ e2.symm)) with
      h0 | ⟨a, ha, h0⟩
    · exact h0 ▸ zero_mem _
    · obtain ⟨o, rfl⟩ := exists_of_integral e (isUnit_ownAt ex.nch w) (ha ▸ hζ)
      rw [h0, algebraMap_smul]
      exact Submodule.smul_mem _ o ht
  | zero => exact rd.map_zero ▸ zero_mem _
  | add u v _ _ hu hv => exact rd.map_add u v ▸ add_mem hu hv
  | smul a y _ hy =>
    obtain ⟨o, ho⟩ := hint a
    have e1 : rd (a • y) = o • rd y := by
      rw [← algebraMap_smul (FractionRing (ex.nch.Oe w)) o, ho]
      exact rd.map_smulₛₗ (a : D.what₂.LL) y
    exact e1 ▸ Submodule.smul_mem _ o hy
theorem baseLe_of_cusp_decay_and_ray_class_field : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ :=
  fun _ _ _ => _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ _ hr hm _ hw _ _ _ _ _ hf hcan => _root_.GlobalTheory.BigOn.Exp.realBase_le_baseLat_of_fit_can hr hm.2.2 hw hf hcan
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem colsStd_of_bWit_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (h : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    q.w.I.Ok ∧ Nonempty (GlobalTheory.Mem.Col2.TC.Pins q.B q.w.px) ∧ GlobalTheory.Mem.Col2.TC.IsTw q.w.I ∧
      Nonempty (GlobalTheory.Mem.Col2.TC.StdC q.w.I q.w.l q.Z b.R.T.cols) ∧ _root_.GlobalTheory.AdForm.TwStdAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  have hs := h.recPin.s
  refine ⟨q.w.ok, ⟨q.w.pins⟩, q.x.pin.isTw, ⟨?_⟩, ?_⟩
  · have e : b.R.T.cols = q.x.col.C := hs.cols
    rw [e]
    exact q.x.col.std
  · obtain ⟨he, hstd⟩ := hs.tw
    exact ⟨q.w.l0, _, he, (eqRec_heq _ _).symm, hstd⟩
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMinGenusBound
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
namespace GlobalTheory.CovGminTop
section Abstract
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Abstract
section Point
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem covering_gmin_of_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := GlobalTheory.CovGmin.minimal_level_cover_is_good hP
  refine Closed.imp (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and ((_root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)
end GlobalTheory.CovGminTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  first | exact @_root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | exact _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | (intros; apply _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTie
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTie
set_option synthInstance.maxHeartbeats 200000

section
open Matrix NumberField
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace GlobalTheory.QuotientNormCoisometry
section Bound
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open _root_.Formalism.L2 _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links _root_.Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Bound
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize in
theorem leafHeightMapBound_tie_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  intro hB hS hI
  obtain ⟨CF0, hI⟩ := hI
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hI⟩ := hI CF hCF
  obtain ⟨e1, he1, hS⟩ := hS
  refine ⟨e1, he1, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := hS eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨x1, hx1⟩ := hK Fm CH hc hL
  refine ⟨max C0 (max CF 0), fun C hC => ?_⟩
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x0, hx0⟩ := hI eps C (le_of_max_le_left hC)
  refine ⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hset := hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser
  have key := hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset
    a.ch ha.ok.is a.atScale ha.ok.field
  have hWF := (hB p hp).1
  have hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL,
      IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧
      ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ *
        (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹ =
        ((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding := fun v =>
    Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)
  have k3 := key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')
  rw [htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]
  exact k3.trans (bound_le d hC0 hCF')
end GlobalTheory.QuotientNormCoisometry
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTieStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafHeightMapBound_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  first | exact @_root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | exact _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | (intros; apply _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK <;> assumption)
end
end
end
