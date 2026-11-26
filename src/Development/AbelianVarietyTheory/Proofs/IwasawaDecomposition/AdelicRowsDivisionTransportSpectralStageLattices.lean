module

public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicRowsDivisionOverReplacedLaterStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicRowsDivisionOverReplacedLaterStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  exact GlobalTheory.Mem.R3.Rw.Mv.rowsAre_refill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStages
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem rxs_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  intro K B f T w Z Wt p0 t S' N h t' hs ⟨x⟩
  have hstd : t'.r.z.Std := (GlobalTheory.T.standardReading_transport_and_extension_trans).1 B f T w Z (SRe.upL Z S' N h) t.hX Wt t.r.z t'.r.z hs.Xg hs.tr hs.R hs.core x.std
  obtain ⟨hX', r', exAt', inGeo', grpAt', grp', mu'', exact', untw', emt0', emt', etaF', rowInt', idx'⟩ := t'
  obtain ⟨z', holds', Y', Z'', tup_ix'⟩ := r'
  obtain @⟨Xg', tr', core', alg', alg_eq', R', cG', geo', pins', lev', idG', good', mu', le', Ks'⟩ := z'
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hcG := hs.cG
  have htup := hs.tup
  have hjA := hs.jA
  have hjA0 := hs.jA0
  have heMt := hs.eMt
  clear hs
  dsimp only at hXg htr hcore hR hcG htup hjA hjA0 heMt hstd
  subst hXg htr
  have hc := eq_of_heq hcore
  subst hc
  have ha : @Eq _ alg' t.r.z.alg :=
    Algebra.algebra_ext _ _ fun r => B.embLL.injective ((alg_eq' r).trans (t.r.z.alg_eq r).symm)
  subst ha
  have hr := eq_of_heq hR
  cases hr
  have hg := eq_of_heq hcG
  cases hg
  cases Y' with
  | mk tup' tupT' tupT_tup' tupTie' tup0' muAt' hm' hTop' hinj' Ish' Iz' IL' Kc' PY' PW' eFT' ιW' tied' prtE' prtE0' prtWE' xi'
      isomFin' frameMatch' hF' stdPsi' jA' jA0' eMt' => ?_
  dsimp only at htup hjA hjA0 heMt
  have e1 := eq_of_heq htup
  cases e1
  have e2 := eq_of_heq hjA
  cases e2
  have e3 := eq_of_heq hjA0
  cases e3
  have e4 := eq_of_heq heMt
  cases e4
  exact ⟨{
    all := {
      jA := (by with_unfolding_all exact (x.all.jA :))
      jA0 := (by with_unfolding_all exact (x.all.jA0 :))
      eMt := (by with_unfolding_all exact (x.all.eMt :))
      formsA := (by with_unfolding_all exact (x.all.formsA :))
      latA := (by with_unfolding_all exact (x.all.latA :))
      formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
      latA0 := (by with_unfolding_all exact (x.all.latA0 :))
      formsL := (by with_unfolding_all exact (x.all.formsL :))
      latL := (by with_unfolding_all exact (x.all.latL :))
      cen := (by with_unfolding_all exact (x.all.cen :)) }
    jA_use := (by with_unfolding_all exact (x.jA_use :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact (x.movedReadingSameMaps_baseReading_agrees :))
    eMt_use := (by with_unfolding_all exact (x.eMt_use :))
    e := (by with_unfolding_all exact (x.e :))
    eMt0 := (by with_unfolding_all exact (x.eMt0 :))
    eMtTw := (by with_unfolding_all exact (x.eMtTw :))
    crd := (by with_unfolding_all exact (x.crd :))
    io := (by with_unfolding_all exact (x.io :))
    sha := (by with_unfolding_all exact (x.sha :))
    laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(SRe.upL Z S' N h).W, (SRe.upL Z S' N h).V, (SRe.upL Z S' N h).S, (SRe.upL Z S' N h).N, (SRe.upL Z S' N h).G⟩ (K := t.r.z.core.toCore) x.laws) :))
    canon := (by with_unfolding_all exact (x.canon :))
    rank := (by with_unfolding_all exact (x.rank :))
    pb := (by with_unfolding_all exact (x.pb :))
    std := (by with_unfolding_all exact (hstd :)) }⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCompatibilities_transport_replacedStages : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  first | exact @GlobalTheory.Mem.R3.Rw.Up.rxs_up | exact GlobalTheory.Mem.R3.Rw.Up.rxs_up | (intros; apply GlobalTheory.Mem.R3.Rw.Up.rxs_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Up

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T₀ D.R.m}

theorem exists_mjHTie_of_eq (F : Face3 D A3) (Xd : DivX D) {X X' : Cx.CxData A3.fam3.amb3} (e : X' = X)
    (jW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (jW0 : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (hj : HEq jW jW0)
    (eW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (h1 : ∀ (i : Fin D.R.m) x, Xd.jM ((i : ℕ) + 1) (eW i x) = jW i x)
    (h2 : ∀ i : Fin D.R.m, HLatTie (Xd.MjH ((i : ℕ) + 1)) ((A3.indefDown (X'.data F.cr false)).M i)
      ((A3.indefDown (X'.data F.cr false)).XW i) (eW i)) :
    ∃ J, MjHTie D A3.A Xd (A3.indefDown (X.data F.cr false)) jW0 J := by
  subst e
  cases hj
  exact ⟨⟨eW⟩, ⟨h1, h2⟩⟩

end GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.Up.mjAre_back : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  intro K B f T w Z hX Wt p0 r S' N h r'
  obtain ⟨z', hold', Y', Z', tix⟩ := r'
  intro hz
  change z' = _ at hz
  subst z'
  intro hj Y hY
  letI : Algebra (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).core.Q.c.F
      (w.st (SRe.upL Z S' N h)).toD7.what₂.LL :=
    (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).alg
  change HEq Z'.jW r.Z.jW at hj
  change MjAre Z' Y at hY
  obtain ⟨J', t'⟩ := hY
  have e := toCx3_eq (Up.refUp Z S' N h).to (iK := r.z.alg) r.z.R r.z.F
  with_unfolding_all
    exact exists_mjHTie_of_eq r.z.F (divBack Y) e.symm Z'.jW r.Z.jW hj J'.eW t'.j_eq t'.hlat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHermitianLattices_replacedStages_eq :
    ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T)
      (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
      (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W)
      (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
      (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _)
        (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)),
      r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z →
        HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)),
          MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) :=
  @GlobalTheory.Mem.R3.Rw.Up.mjAre_back
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem rows_up_at : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  let ix : w.C.Tup ≃ w.I.ι := by
    with_unfolding_all exact (Equiv.refl w.C.Tup :)
  have transported := GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages
    B w.C Z (refUp Z S' N h) w.px w.I t.hX T Wt ix p0
    (by with_unfolding_all exact (t.r :))
  rcases transported with
    ⟨⟨z', hold', Y', Z'', tup'⟩, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  subst hz
  let r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I t.hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    ⟨Mv.cpDat (refUp Z S' N h).to (refUp Z S' N h).same t.r.z, hold', Y', Z'', tup'⟩
  have eW1 := Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (refUp Z S' N h).to (refUp Z S' N h).same t.r.z (F0K K.s (w.D (SRe.upL Z S' N h)))
  let t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    { hX := t.hX
      r := r'
      exAt := Mv.cp_exAt _ _ _ t.exAt
      inGeo := Mv.cp_inGeo _ _ _ t.inGeo
      grpAt := grpAt_up S' N h t.grpAt
      grp := t.grp
      mu := muIsW_up S' N h t.mu
      exact := (@Eq.trans (Set (@Rows.Places.Pl B.LL B.instLL B.places)) Wt (@Dat.W1 (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w Z))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@RowsT.exact B f T K w Z Wt p0 t) (@Eq.symm (Set (@Rows.Places.Pl (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.LL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.instLL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.places)) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) eW1))
      untw := (t.untw)
      emt0 := (t.emt0)
      emt := (t.emt)
      etaF := t.etaF
      rowInt := rowInt_up S' N h t.rowInt
      idx := fun Y hY => idxDefs_up (Z := Z) (S' := S') (N := N) (h := h) Y
        (t.idx (divBack Y) (GlobalTheory.T.liftHermitianLattices_replacedStages_eq K B f T w Z t.hX Wt p0 t.r S' N h r' rfl h13 Y hY)) }
  have hs : RowsSame t t' :=
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, (HEq.refl t.r.z.cG), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  refine ⟨t', hs, (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo)) :)), ?_, GlobalTheory.T.rowCompatibilities_transport_replacedStages K B f T w Z Wt p0 t S' N h t' hs⟩
  exact (by with_unfolding_all exact ((congrArg (fun e => ({ (SRe.pkOf t).up Z S' N h with eE := e } : SRe.RowPk (SRe.upL Z S' N h).D)) (eq_of_heq h8)) :))

theorem rows_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := fun K B f T w Z Wt p0 t S' N h =>
  Exists.elim (rows_up_at K B f T w Z Wt p0 t S' N h) fun t' ht' =>
    ⟨Tr.baseLevelRowSideTransport (refUp Z S' N h) p0, t', ht'⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  exact GlobalTheory.Mem.R3.Rw.Up.rows_up K B f T w Z Wt p0 t S' N h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespond
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TSq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Generic

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_sqGen (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        val u r z (fun q _ => J q) = val t r z J ^ 2 := by
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε ε) (flatφ (fun _ : Fin 1 => 𝟙 X) φ)
      (flatε (fun _ : Fin 1 => (2 : ℤ)) ε) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
    rw [zpow_mul, zpow_two]
  obtain ⟨s, hs, hv⟩ := exists_gen hL hF (LB.mulGen L φ ε φ ε t t) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht)
  refine ⟨nest L _ _ _ _ s, nest_isGen hs, fun Z r z J hJ => ?_⟩
  rw [val_nest hs r (GlobalTheory.SqCube.good_sq hJ) hJ, hv _ _ z J hJ, val_mul hJ]
  simp only [GlobalTheory.SqCube.adj_sq hL hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (sq _).symm

theorem eq_of_ratio_inv {Y' S₀ : Scheme.{0}} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) [Flat m]
    [Surjective m] [QuasiCompact m] (p : Y ⟶ S₀) (e₀ : S₀ ⟶ Y') (he : (e₀ ≫ m) ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (u u' : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε))
    (hu : u.IsGen) (hu' : u'.IsGen)
    (hinv : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ Y') (z : Z), r ≫ m = r' ≫ m → ∃ J, Good L z J ∧
      val u r z J * (val u' r z J)⁻¹ = val u r' z J * (val u' r' z J)⁻¹)
    (h₁ : ∀ y : S₀, ∃ J, Good L y J ∧ val u e₀ y J = val u' e₀ y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := fun k => m ≫ (PEmpty.elim k : Y ⟶ X))
    (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have tv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J' : (Z ⟶ X) → L.ι), val t r z J = val t r z J' :=
    fun Z r z J J' => by
      rw [val_of t r z J PEmpty.elim (fun k => k.elim), val_of t r z J' PEmpty.elim (fun k => k.elim)]
  have rv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      val t r z J = val u r z J * (val u' r z J)⁻¹ :=
    fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv]
  obtain ⟨v, hvg, hvv⟩ := CoordCompare.exists_gen_of_val_eq hL (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim m t ht
    (fun Z r r' z J hJ h => by
      obtain ⟨J₀, hJ₀, e⟩ := hinv Z r r' z h
      rw [tv Z r z J J₀, tv Z r' z J J₀, rv _ _ _ _ hJ₀, rv _ _ _ _ hJ₀, e])
  have one := gen_unique hL p (e₀ ≫ m) he hp hvg (u' := LB.oneGen L (Y := Y))
    (isGen_of_gm _ fun y j j' _ _ => (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _)
      (map_one _)).trans (_root_.mul_one _)))) (fun y J hJ => by
      obtain ⟨J₀, hJ₀, e⟩ := h₁ y
      rw [hvv _ e₀ y J hJ, val_one, tv _ e₀ y J J₀, rv _ _ _ _ hJ₀, e, mul_inv_cancel])
  have := (rv Z r z J hJ).symm.trans ((hvv Z r z J hJ).symm.trans ((one Z (r ≫ m) z J hJ).trans (val_one _)))
  exact mul_inv_eq_one.1 this

end Generic

end GlobalTheory.TSq

namespace GlobalTheory.TSq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem sq_ratio {V : Type} [CommGroup V] {a b a' b' O : V} (h : b * a⁻¹ = b' * a'⁻¹) :
    a ^ 2 * (O * b ^ 2)⁻¹ = a' ^ 2 * (O * b' ^ 2)⁻¹ := by
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e ⊢
  linear_combination (norm := abel) (-2 : ℤ) • e

end GlobalTheory.TSq


open GlobalTheory.TSq ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.torus_coord_squares_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' Φ w hw hΦ hpG xe hMatch β hc e Z r z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM := DVR.linComb_isLB (Y := D.toPre.P.A.left) _ hL (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)
  have hM' := DVR.linComb_isLB (Y := D'.toPre.P.A.left) _ hL' (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
    (fun _ => 2)
  have hp' : (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := Over.OverMorphism.ext (hpG e)
  haveI : Mono Φ.hom.left := ⟨fun a b h => by
    have k := congrArg (· ≫ Φ.inv.left) h
    simp only [Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id] at k
    exact k⟩
  haveI := (U.gt e).q_flat
  haveI := (U.gt e).q_surj
  haveI := (U.gt e).q_affine
  obtain ⟨T, hT, vT⟩ := exists_sqGen hL ((U.gt e).t (xe (2 • β))) ((U.gt e).t_gen _)
  obtain ⟨T', hT', vT'⟩ := exists_sqGen hL' ((U'.gt e).t (2 • β)) ((U'.gt e).t_gen _)
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_up ((isGen_iff w).1 hw) hM hM' T' hT'
  have hφ : ∀ k, D.toPre.Oφ (U.gt e).pG (xe (2 • β)) k =
      (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R _ e)).map (U.gt e).q) (D.toPre.prBe _ e) _ k).symm
  have hψ : ∀ k, D'.toPre.Oφ (U'.gt e).pG (2 • β) k ≫ Φ.hom.left = D.toPre.Oφ (U.gt e).pG (xe (2 • β)) k := by
    intro k
    rw [CoordCompare.Oφ_comp_hom, hp', hc]
    rfl
  obtain ⟨a, ha, va⟩ := exists_gen hM
    (φ' := fun k => (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) (ε' := Oinvε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by rw [hφ k]) T hT
  obtain ⟨b, hb, vb⟩ := exists_gen hM
    (φ' := fun k => (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) (ε' := Oinvε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by rw [hψ k, hφ k]) t₁ ht₁
  have va' : ∀ {Z : Scheme.{0}} (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J → val a r z (fun q _ => J q) = val ((U.gt e).t (xe (2 • β))) r z J ^ 2 :=
    fun r z J hJ => (va _ r z _ (GlobalTheory.SqCube.good_sq hJ)).trans (vT _ r z J hJ)
  have vb' : ∀ {Z : Scheme.{0}} (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      val b r z (fun q _ => J q) = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
    intro Z r z J J' hJ hJ'
    have hJP := GlobalTheory.SqCube.good_sq hJ
    have hJP' := GlobalTheory.SqCube.good_sq hJ'
    rw [vb _ r z _ hJP, ← vT' _ r z J' hJ']
    refine (hv₁ _ r z _ _ (hJP.mem _ r) (hJP'.mem _ r)).trans ?_
    simp only [pw, ExpTrans.om, Category.assoc]
    rfl

  have hinv : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z),
      r ≫ (U.gt e).q.left = r' ≫ (U.gt e).q.left → ∃ JP, Good (LB.LinComb D.toPre.P.L (K := Fin 1)
        (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)) z JP ∧
        val a r z JP * (val b r z JP)⁻¹ = val a r' z JP * (val b r' z JP)⁻¹ := by
    intro Z r r' z h
    choose J₀ hJ₀ using fun ψ : Z ⟶ D.toPre.P.A.left => exists_chart hL (ψ z)
    choose J₀' hJ₀' using fun ψ : Z ⟶ D'.toPre.P.A.left => exists_chart hL' (ψ z)
    have hJ₀ : Good D.toPre.P.L z J₀ := hJ₀
    have hJ₀' : Good D'.toPre.P.L z J₀' := hJ₀'
    obtain ⟨h₁, h₂⟩ := CoordCompare.ratio_invariant (U.gt e) (U'.gt e) Φ.hom hp' (xe (2 • β)) (2 • β)
      (fun Z r z J J' hJ hJ' c c' => hMatch e Z r z J J' hJ hJ' c c' (2 • β)) r r' z J₀ J₀' hJ₀ hJ₀' h
    refine ⟨fun q _ => J₀ q, GlobalTheory.SqCube.good_sq hJ₀, ?_⟩
    rw [va' r z J₀ hJ₀, va' r' z J₀ hJ₀, vb' r z J₀ J₀' hJ₀ hJ₀', vb' r' z J₀ J₀' hJ₀ hJ₀']
    have ho : (∏ κ, ExpTrans.om w z (fun q _ => J₀ q) (fun q _ => J₀' q)
        (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) = ∏ κ, ExpTrans.om w z (fun q _ => J₀ q)
        (fun q _ => J₀' q) (r' ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ :=
      Finset.prod_congr rfl fun κ _ => by rw [CoordCompare.Oφ_congr (2 • β) (U'.gt e).pG r r' h₁ κ]
    rw [ho]
    exact sq_ratio h₂
  have hone : ∀ y : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left, ∃ JP,
      Good (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)) y JP ∧
      val a (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y JP =
      val b (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y JP := by
    intro y
    choose J₀ hJ₀ using fun ψ : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ⟶
      D.toPre.P.A.left => exists_chart hL (ψ y)
    choose J₀' hJ₀' using fun ψ : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ⟶
      D'.toPre.P.A.left => exists_chart hL' (ψ y)
    have hJ₀ : Good D.toPre.P.L y J₀ := hJ₀
    have hJ₀' : Good D'.toPre.P.L y J₀' := hJ₀'
    refine ⟨fun q _ => J₀ q, GlobalTheory.SqCube.good_sq hJ₀, ?_⟩
    have u₁ : val ((U.gt e).t (xe (2 • β))) (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ = 1 :=
      TorusCoord.val_unit (U.gt e) (Z := Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))) _ hJ₀
    have u₂ : val ((U'.gt e).t (2 • β)) (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀' = 1 :=
      TorusCoord.val_unit (U'.gt e) (Z := Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))) _ hJ₀'
    have a₁ := va' (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ hJ₀
    have b₁ := vb' (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ J₀' hJ₀ hJ₀'
    refine (a₁.trans ((congrArg (· ^ 2) u₁).trans (one_pow 2))).trans (Eq.trans ?_ b₁.symm)
    refine Eq.trans ?_ (congrArg (_ * ·) ((congrArg (· ^ 2) u₂).trans (one_pow 2))).symm
    rw [_root_.mul_one]
    let Tt := (Over.map (thick R (maximalIdeal R) e)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))))
    let f := fun ψ => ExpTrans.om w y (fun q _ => J₀ q) (fun q _ => J₀' q) ψ
    have e0 : ∀ k, (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) k =
        D'.toPre.Oφ (1 : Tt ⟶ D'.toPre.P.A) (2 • β) k :=
      fun k => (WeightPf.Oφ_comp ((Over.map (thick R _ e)).map 1) (U'.gt e).pG _ k).trans
        (congrArg (D'.toPre.Oφ · _ k) (TorusCoord.im_one (U'.gt e)))
    refine Eq.symm ((Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_)
    rw [Fin.prod_univ_four]
    show f ((1 : Tt ⟶ D'.toPre.P.A) * (toUnit Tt ≫ D'.toPre.c (2 • β))).left ^ (-1 : ℤ) *
      f (toUnit Tt ≫ D'.toPre.c (2 • β)).left ^ (1 : ℤ) * f (1 : Tt ⟶ D'.toPre.P.A).left ^ (1 : ℤ) *
      f (1 : Tt ⟶ D'.toPre.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have key := eq_of_ratio_inv hM (fun k => D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) Oinvε (U.gt e).q.left
    (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left
    (Over.w ((1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
      thickObj R (maximalIdeal R) e G) ≫ (U.gt e).q))
    (GlobalTheory.globalFns_holds _ _ (TLinPf.isAb_pullback _ _ D.toPre.P.isAb)).2 a b ha hb hinv hone Z r z
    (fun q _ => J q) (GlobalTheory.SqCube.good_sq hJ)
  rw [va' r z J hJ, vb' r z J J' hJ hJ'] at key
  exact key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespondStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coord_squares_correspond' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  first | exact @GlobalTheory.torus_coord_squares_correspond | exact GlobalTheory.torus_coord_squares_correspond | (intros; apply GlobalTheory.torus_coord_squares_correspond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors
noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dite_eq_right (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dite_eq_left hk, dite_eq_left hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dite_eq_right hk, dite_eq_right hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dite_eq_right]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dite_eq_left h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinorsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m), LeftInv D c → InBlock c u → (∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) → ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.CellLU.exists_cell | exact GlobalTheory.FlagEmb.CellLU.exists_cell | (intros; apply GlobalTheory.FlagEmb.CellLU.exists_cell <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Overlap

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_fieldPoint {A : Type} [CommRing A] (y : Sp A) :
    ∃ (k : Type) (_ : Field k) (ψ : A →+* k), ∀ q : Sp k, spMap ψ q = y := by
  refine ⟨(show PrimeSpectrum A from y).asIdeal.ResidueField, inferInstance, algebraMap _ _, fun q => ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap _ (show PrimeSpectrum _ from q).asIdeal = _
  rw [show (show PrimeSpectrum _ from q).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
  exact Ideal.ker_algebraMap_residueField _

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {ι : Type} {c c' : Let m → ι → S}
    (h : InBlock c c') (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_lform {ι : Type} {M k : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q : Fin (plN M k + 1)) :
    φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

theorem range_inter_cellOpen_subset : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∀ b' w', Set.range (h b' w') ∩ (W : Set P) ⊆ Set.range (h b w) := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hc hp b w W hW b' w'
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  obtain ⟨k, _, ψ', hψ'⟩ := exists_fieldPoint y
  have hz : ∀ q : Sp k, (spMap ψ' ≫ h b' w') q = h b' w' y := fun q => by
    rw [Scheme.Hom.comp_apply, hψ']
  obtain ⟨φ, hφ, hne⟩ := (hW k (spMap ψ' ≫ h b' w')).1 (by
    rintro _ ⟨q, rfl⟩
    rw [hz]; exact hy)
  rw [Category.assoc, hp.base] at hφ
  have hφ' : spMap φ ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← hφ, cbase, ← Category.assoc, spMap_spMap]
  have hu : InBlock (fun z => φ ∘ c b z) (fun z => ψ' ∘ uvec (c b') w' z) := by
    have := inBlock_cellVec (hc.compat k b b' φ _ hφ') w' (ψ' ∘ MvPolynomial.X)
    convert this using 2 with z
    exact map_cellVec ψ' _ w' _ z
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  obtain ⟨x, d, hd, ht⟩ := GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors T m k M _ _ _ w ((hc.inv b).map φ) hu (fun τ j hj => by
    obtain ⟨hv, e⟩ := hp.plk b' w' (stdEn τ j hj)
    have := hne τ j hj _ _ _ (by rw [Category.assoc, e, spMap_pt])
    rw [map_plk] at this
    simpa only [map_lform] using this)
  have hψ : ∀ z, (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) ∘ uvec (c b) w z =
      cellVec (fun z => φ ∘ c b z) w x z := fun z => by
    refine (map_cellVec _ _ w _ z).trans ?_
    congr 1
    · funext z r; simp
    · funext r; simp
  have key := GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hc hp k b b' w w' (MvPolynomial.eval₂Hom φ x) ψ' d
    (by rw [hφ, cbase, ← Category.assoc, spMap_spMap, MvPolynomial.eval₂Hom_comp_C]) hd
    (by simpa only [hψ] using ht)
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨spMap (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) q, by
    rw [← hz q, ← key, Scheme.Hom.comp_apply]⟩

end GlobalTheory.FlagEmb.Overlap
end
