module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtSize

theorem leastSplitAuxiliaryPrime_lt_scaleBound {K : Ctx} {X : Stages} (hO : K.Over X.B.toPre) {C5 c6 Cb : ℝ} (hG : K.Good C5 c6 Cb) :
    ((GlobalTheory.ChiGrid.q0 X.toD7 : ℕ) : ℝ) < K.s.X' := by
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  have hmem := hOk.small.1
  rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
  · exact absurd hi (hOk.small.2.2.2.1 i)
  · exact hlt


end GlobalTheory.Mem.AtSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightOnePlacesAreTwistPlacesOfWitness
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem finite_T_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) : Finite a.x.T := by
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hfin



end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistsAtLinked
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowEx.FrmW

open GlobalTheory.Mem.R3 _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}


set_option maxHeartbeats 1000000 in
theorem frame_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) :
    x.R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero x.R.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ T.set f, HEq (x.R.toRealDat.toLevCh.xiH u) ξ := by
  obtain rfl := eq_of_heq hx
  have hz := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z _ _ t.r.z
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero R.toRealDat.toLevCh ∧
        ∀ u, ∃ ξ ∈ T.set f, HEq (R.toRealDat.toLevCh.xiH u) ξ) a.pack
  exact e.mpr ⟨hz.2.1, hz.1, fun u => ⟨_, hz.2.2.2 u, HEq.rfl⟩⟩

end GlobalTheory.RowEx.FrmW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEListPinPt
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open _root_.Formalism.L2.Host _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

theorem listPin_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : GlobalTheory.Mem.R3.TwArgs ex t) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 a.x.R.toRealDat.toLevCh CF bb := by
  have e := congrArg (fun s : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 (w.st Z).toD7.what₂.LL G Pl0 I0 (List ℕ) T0 (w.st Z).toD7.R.m) (C : Formalism.L2.Pj.CoreJ (w.st Z).toD7)
        (_ : Algebra C.Q.c.F (w.st Z).toD7.what₂.LL) (R : RealDat3 (w.st Z).toD7 A3 C.Q.c.F) (_ : Face3 (w.st Z).toD7 A3),
        G0 R.Pg (w.st Z).toD7.R.r ≃* G0g (w.st Z).toD7.nd =>
      match s with
      | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => GlobalTheory.HeightCounting.Up.ListPin (w.st Z).toD7 R.toRealDat.toLevCh CF bb) a.pack
  exact cast e.symm h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeoAtGridA
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFld
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRowsDlog
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRows
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.AtSize
set_option maxHeartbeats 1000000 in
theorem eventually_sizeRows_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), fun K h1 h2 h3 h4 hx β _ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hy44, hy8⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (GlobalTheory.Plug.hostArith_bpt β)
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hq : ((GlobalTheory.ChiGrid.q0 β.D : ℕ) : ℝ) < β.O.L.sc.X' := by
    rw [hsc]
    exact leastSplitAuxiliaryPrime_lt_scaleBound β.c.isOver hG
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of N.params N.parT (N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1) N.sizes
    N.win.1.1 N.win.2.1.1 N.win.2.1.2 N.win.2.2.1 N.g_le hq N.ccK_top ?_ (by rw [hsx]; exact hy44)
  rw [hsx, hse]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) hy8 (by positivity)
end GlobalTheory.Mem.AtSize
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightOnePlacesFiniteOfWitness
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 4000000 in
theorem zscale_f0_of_witness_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hsc : q.O.L.sc = K.s) :
    HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
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
set_option maxHeartbeats 4000000 in
theorem weight_one_places_finite_of_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ)
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → q.O.L.sc = K.s →
    (∀ v, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F 0 0) v → v ∈ b.B.Q.Rl.twPl) ∧
      b.B.Q.Rl.toRealDat.ExAt ∧ Finite b.P.T := by
  intro hL p K q c b w hsc
  have hZ := _root_.GlobalTheory.Mem.Top.Bl.zscale_f0_of_witness_alt q b w hsc
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  letI := a.x.grp
  letI := a.x.fin
  letI : Algebra (↥a.x.core.Q.c.F) (q.w.D q.Z).what₂.LL := a.x.alg
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a b.R b.S y.y hZ
  have hP : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree r.B.Q ∧ r.B.Q.Rl.toRealDat.ExAt ∧ Finite r.P.T) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y) :=
    ⟨h3, y.intersectionNumber_baseChange.aux.ex, finite_T_of_twArgs a⟩
  rw [← y.eq] at hP
  exact ⟨hP.1.w1 0 0, hP.2.1, hP.2.2⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitFrameTwists
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → b.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero b.B.Q.Rl.toRealDat.toLevCh ∧ ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (b.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ := by
  intro hL p K q c b w
  have h2 := GlobalTheory.RowEx.FrmW.frame_of_args w.a w.x w.ax
  have e := congrArg (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero r.B.Q.Rl.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (r.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ) w.y.eq
  exact e.mpr h2
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ListPinRpk
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt

open Formalism.BasicNotions GlobalTheory.EX.OB
open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem listPin_rpk_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : GlobalTheory.Mem.R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S)
    (r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S)
    (hr : r = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin D x.R.toRealDat.toLevCh CF bb) :
    GlobalTheory.HeightCounting.Up.ListPin D r.B.Q.Rl.toRealDat.toLevCh CF bb := by
  subst hr
  exact h

end GlobalTheory.Mem.LiteralAutomorphy.PinPt
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTestSetting
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PrimIn
theorem rowTest_setting_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q → (∀ w, (B.Q.Rl.toCx3 B.Q.F).W1 B.Q.F.cr (B.Q.Rl.num B.Q.F 0 0) w → w ∈ B.Q.Rl.twPl) → B.Q.Rl.toRealDat.ExAt → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.GLq.ESerTie D → Finite P.T → GlobalTheory.RowClaim.HidaSetting L B.Q.Rl.toRealDat B.Q.F.lv2 := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hp _hW hEx hsz hser hfin
  have hC := B.Q.charW
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak B.Q.Rl B.Q.F hC hEx).1
  exact
    { size := hsz
      eser := hser
      host := B.Q.host
      hF := hp.hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := hp.qGuard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := B.Q.stdChar
      stdX := B.Q.stdX
      betaX := hp.betaStd.2 }
end GlobalTheory.PrimIn
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem eventually_sizeRows_and_logDeriv_le_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) →
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L ∧ |β.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps := by
  refine (_root_.GlobalTheory.Mem.AtSize.eventually_sizeRows_alt hL p).mono fun κ K _ H β hq => ⟨H β hq, ?_⟩
  have h := β.val.dlog
  rw [β.sc] at h
  exact h
set_option maxHeartbeats 1000000 in
theorem rowE_full_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b.part t).pt.R.toRealDat G := by
  refine (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.eventually_sizeRows_and_logDeriv_le_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)).mono fun κ K hk H β hq c b hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h2 : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ :=
    congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) he
  have hL' : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows q.O.L ∧ |q.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps :=
    Eq.ndrec (motive := fun s : Σ D : D7, Obj D => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows s.2.L ∧ |s.2.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps) (H β hq) h2
  have hsc0 : β.O.L.sc = K.s := β.sc
  have hsc : q.O.L.sc = K.s := Eq.ndrec (motive := fun s : Σ D : D7, Obj D => s.2.L.sc = K.s) hsc0 h2
  have hA : GridA CF K q.B q.f q.T := q.x.nx.2.2.down
  have hG : GridAt K.s CF (q.w.st q.Z) q.f (q.T.set q.f) := hA _ _ _ _ _ _
  suffices key : ∀ t : b'.Comparison₂, (b'.part t).pt.CompatibilityConditions → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF,
      ∃ G : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b'.part t).pt.R.toRealDat G by
    have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
      ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧
        G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin s.1.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧
        Full (s.2.2.part t).pt.R.toRealDat G) he
    exact cast h1.symm key
  intro t ht G₀
  obtain ⟨hW1, hEx, hfin⟩ := _root_.GlobalTheory.Mem.Top.Bl.weight_one_places_finite_of_witness hL _ K q c b' w hsc
  obtain ⟨hC, hoff, hxi⟩ := _root_.GlobalTheory.RowEx.frame_eq_and_twistPlacesOffPrimeQZero_of_bWit hL _ K q c b' w
  have hset : GlobalTheory.RowClaim.HidaSetting q.O.L b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 :=
    _root_.GlobalTheory.PrimIn.rowTest_setting_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b'.B t.pins hW1 hEx hL'.1 ht.eSer hfin
  have hrec : GlobalTheory.SqTop.Rec q.O.L := ⟨hL'.1, hset.host, hset.hF, by rw [hsc]; exact hL'.2⟩
  have hb : (b'.part t).pt.Z.b = K.s.b := by
    have h0 : (b'.part t).pt.Z.b = q.O.L.sc.b := rfl
    rw [h0, hsc]
  have gen : ∀ z : ℝ, z = K.s.b → ∀ G₀ : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩,
      ∃ G : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full b'.B.Q.Rl.toRealDat G := by
    rintro z rfl G₀
    obtain ⟨G, hk, hF⟩ := @hG q.O.L hsc hrec _ _ _ _ _ _ _ _ _ b'.B.alg b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 hset hC hoff hxi G₀
    exact ⟨G, congrArg Prod.fst hk, congrArg (fun x => x.2.1) hk, fun a => congrFun (congrArg (fun x => x.2.2) hk) a, hF⟩
  exact gen _ hb G₀
set_option maxHeartbeats 4000000 in
theorem rowE_pinned_grid_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) : RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G₀) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hsc : β.O.L.sc = K.s := β.sc
  have hsc' : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => s.2.1.L.sc) he
    exact this.symm.trans hsc
  have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.CompatibilityConditions →
    ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 s.1) ∧
      GlobalTheory.LamTie.IsLamTieFull s.1.ntw (GlobalTheory.BigTop.Fun.lamOf G₀)) he
  refine cast e.symm ?_
  intro t _
  obtain ⟨nl⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2.1
  have hp : GlobalTheory.HeightCounting.Up.ListPin (q.w.st q.Z).toD7 q.x.what₂.r.z.R.toRealDat.toLevCh CF K.s.b := nl.2.down
  have h1 := GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_twArgs w.a hp
  rw [eq_of_heq w.ax] at h1
  have h2 := _root_.GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_rpk_alt w.y.y (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b') w.y.eq h1
  rw [← hsc'] at h2
  exact h2
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistsAtLinked
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem Q_eq_alt (q : WPt p.s K) {w w' : (q.w.D q.Z).what₂.places.Pl} (hw : Twisted (q.w.D q.Z) w)
    (hw' : Twisted (q.w.D q.Z) w') (h : SamePair (q.w.D q.Z) w w') :
    q.O.ex.nch.Q w = q.O.ex.nch.Q w' ∧ q.O.ex.nch.k' w = q.O.ex.nch.k' w' := by
  have key : ∀ v v', Twisted (q.w.D q.Z) v → Twisted (q.w.D q.Z) v' → SameBelow (q.w.D q.Z) v v' →
      q.O.ex.nch.Q v = q.O.ex.nch.Q v' ∧ q.O.ex.nch.k' v = q.O.ex.nch.k' v' := by
    intro v v' hv hv' hs
    have m : ∀ u, Twisted (q.w.D q.Z) u → u ∈ q.x.Wt := fun u hu => by
      by_contra hn
      exact hu (q.x.what₂.mu.off u hn)
    have a := q.x.n.Q v (m v hv)
    have a' := q.x.n.Q v' (m v' hv')
    have c := q.x.coh.same v v' fun x hx => hs ⟨x, hx⟩
    exact ⟨a.1.trans (c.1.trans a'.1.symm), a.2.trans (c.2.1.trans a'.2.symm)⟩
  rcases h with h | h
  · exact key w w' hw hw' h
  · have k := key _ w' ((GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw) hw' h
    have c := q.core_data_of_point.a.all.choice.conj w hw
    exact ⟨(congrArg (fun t : TwPack _ => t.2.1) c).symm.trans k.1, (congrArg (fun t : TwPack _ => t.2.2.1) c).symm.trans k.2⟩
theorem twists_at_linked_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot), RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ D O _ _ => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w)) := by
  intro hL p Q
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', -, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c =>
    (fun (D : D7) (O : Obj D) => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w))) s.1 s.2.1) he
  refine cast h1.symm ?_
  obtain ⟨I, -, hI, -⟩ := q.x.good.tw
  exact ⟨fun w hw => ⟨q.O.ex.nch.twI_l w, GlobalTheory.TwistGoodCompare.atPlace_of_tie q.B.coeffGaloisSubfield_isGalois q.O.ex.nch_tie w hw⟩,
    fun w w' hw hw' h => ⟨(_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1, (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).2, twI_eq q.x.good hw hw' (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1⟩, cond_powers hI⟩
end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFld
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
section Transfer
variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end Transfer
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem hasGrid_of_full_field_lamTie (p : PtAt ex Csz) (CF : ℝ) (hp : p.CompatibilityConditions)
    (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hpw : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (G : Grid p CF) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D)) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (hF : Full p.R.toRealDat G) : HasGrid (@Fld) p CF := by
  have hfit := gridFit_of_parts hs hc hpw hp.real.valLL0 h2 hp.real.psiChoice h4
  obtain ⟨W, M, ρ, ξ, cv, rm, S, rp, n, e, c, hIs, hOK, hSq⟩ := hF
  exact ⟨G, W, hIs.weil, hfit, n, ⟨M, ρ, ξ, cv, rm, S, rp, e, c⟩, ⟨hIs, hp.eSer, hOK, hSq⟩⟩
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem rowE_hasGrid_fld_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  intro hL CF N S Γ hN
  refine ((_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.twists_at_linked_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s)).and
    ((_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_pinned_grid_alt hL CF N S Γ hN).and (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_full_grid_alt hL CF N S Γ))).imp fun κ K β c b _ _ _ H t ht => ?_
  obtain ⟨hw1, hw2, hcond, hpow⟩ := H.1
  obtain ⟨G₀, hF₀, hT₀⟩ := H.2.1 t ht
  obtain ⟨G, hv, hw, hch, hFull⟩ := H.2.2 t ht G₀
  exact _root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.hasGrid_of_full_field_lamTie _ CF ht ⟨hw1, fun w w' a b c => (hw2 w w' a b c).2.2⟩ hcond hpow G (fieldHas_of_same hv hch hF₀)
    (lamOf_of_same hw hch ▸ hT₀) hFull
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFldStatement
alias GlobalTheory.T.grid_field_has_lattices_alt :=
  GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_hasGrid_fld_alt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeoAtGridA
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem rowGeo_at_gridA_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) fun Q L => _root_.GlobalTheory.Fc.RL.RowGeometricCondition Q L CF := by
  intro hR hL CF N S Γ hN hD hT
  have hA := _root_.GlobalTheory.T.class_sum_divisor_all_alt hR hL (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ
    (fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h.1).map fun x => x.1) hD
  have hG : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) fun S L => Row S L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) =>
      ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF) :=
    _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (_root_.GlobalTheory.T.grid_field_has_lattices_alt hL CF N S Γ hN))
  obtain ⟨R, r, h⟩ := RowL.and (RowL.and hA hG) hT
  refine ⟨R, r, Row.imp h fun 𝒜 σ _ H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := H.2 Fm hc x hx i
  obtain ⟨a, b, c, d, e⟩ := H.1.1 Fm hc x hx i t
  exact ⟨t, a, b, c, d, e, H.1.2 Fm hc x hx i t c⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeoAtGridAStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_condition_large_grid_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) fun Q L => _root_.GlobalTheory.Fc.RL.RowGeometricCondition Q L CF := by
  first | exact @_root_.GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA_alt | exact _root_.GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA_alt | (intros; apply _root_.GlobalTheory.Mem.LiteralAutomorphy.rowGeo_at_gridA_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCFunOfFun0Fit
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_fun_of_fun0Fit_alt : ∀ Fld : GlobalTheory.BigTop.Fun.FldT, _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigTop.Fun.HasGrid @Fld b.pt CF) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 σ := by
  intro Fld h
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF 𝒜 σ hD hR hG => ?_⟩
  exact _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigTop.Fun.HasGrid @Fld p CF)
    (fun C CH _ _ _ p => (p.S false).FUN (p.N C CH))
    ((h CF hCF).imp fun Fm CH _ a hN =>
      ⟨0, le_rfl, _root_.GlobalTheory.BigTop.Fun.evPt_mono (a hN) fun _ _ _ _ _ b hg C _ => b hg C⟩) 𝒜 σ hD hR hG
end GlobalTheory.Fc.Ind
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Fc.StageOne
theorem rowFun_at_gridA_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.NT.RayField → _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) _root_.GlobalTheory.Fc.S0.FunctionalCondition := by
  intro hDS hHC hCR hCW hRay hFun
  obtain ⟨CF0, hCF⟩ := _root_.GlobalTheory.Fc.Ind.evWC_fun_of_fun0Fit_alt @GlobalTheory.BigTop.Fun.Fld hFun
  refine ⟨CF0, fun CF hle hL N S Γ hN o => ?_⟩
  have hA := _root_.GlobalTheory.T.geometric_condition_large_grid_alt hRay hL CF N S Γ hN o.hDivG o.tie
  obtain ⟨R, hR, h⟩ := RowL.and (RowL.and (RowL.and o.hPA o.hDivG) o.good) hA
  refine ⟨R, hR, h.imp fun 𝒜 σ hsel H => ?_⟩
  obtain ⟨⟨⟨hpa, hdv⟩, hgd⟩, hgeo⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hgeo Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i => hpa Fm hc x hx i)
      (fun Fm hc x hx i => _root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ (hdv Fm hc x hx i)) hgd
      (fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩)
  have key := hCF CF hle 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows
    (GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2.2.2)
  first | exact key | exact ⟨τ', key⟩
end GlobalTheory.Fc.StageOne
end
