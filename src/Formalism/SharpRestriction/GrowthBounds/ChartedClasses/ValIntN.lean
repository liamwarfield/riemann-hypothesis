module

public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
public import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure AtIn where
  Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn (Tw.fm u μ) (j + 1) hj
  Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch

variable {X0 Tw u μ w h Lv}

def AtIn.st (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1)) :=
  stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h)

def AtIn.I (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) : CmpJIn Tw u μ w h Lv := inTw (Z.st Gt)

structure AtHyp (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  ties : ∀ j hj β, LocTiesR hj (Z.Fo j hj) (Z.Lc j hj) (c.embW u w h) β
  hypC : ∀ j hj β, HypTJC ((Z.Lc j hj).t β)
  ok : ∀ j hj, (Z.st Gt j hj).okW w
  twUnit : ∀ j hj β, (Z.st Gt j hj).TwUnit w β
  valIntN : ∀ j hj, (Z.st Gt j hj).ValIntN (c.embW u w h) w
  fin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses
  card : ∀ j (hj : j + 1 ≤ D.R.m), Fintype.card ((Tw.fm u μ).lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem AtHyp.chX {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (((Z.I Gt).at' j hj).st) :=
  chX_stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) (fun β => (A.ties j hj β).sameU) (fun β => (A.ties j hj β).frRat)
    (A.hypC j hj)

end Formalism.MainNotions.G.KAat

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelStabilizers
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KernelStabilizer
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.KernelStabilizer

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.KerInert.SecondKernelInstances

def StabEqRest {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    (KA : TwTie.KerAtMu D c Tw u μ w h Ch) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Nat.card ((D.chTw u μ).stab j (KA.cls j a L)) = Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}


set_option linter.unusedVariables false in
def TieStab0Inst : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j),
    DV.Used D μ → OrbitPlaces.Stab0 D → TieStabAt (Y := Y) u μ cls 0


def TieStabRestIff : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    StabEqRest KA ↔ ∀ j, 1 ≤ j → j ≤ D.R.m → TieStabAt (Y := Y) u μ KA.cls j

def TieStabAllInst : Prop :=
  ∀ (D : D7) (ex : TwForms D) (cc : LatCmp D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D cc ex u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → StabEqRest KA → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ KA.cls j

theorem stabilizer_base_instance : TieStab0Inst := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y cls hU hS La hLa
  rw [hS.2 u μ hU _]
  exact (KA.stab_zero La.1 La.2 (Y.Rep_lat 0 La hLa)).symm

theorem stabilizer_restrict_iff : TieStabRestIff := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y
  constructor
  · intro hR j h1 hj La hLa
    exact hR j h1 hj La.1 La.2 (Y.Rep_lat j La hLa)
  · intro hT j h1 hj a L hL
    have hjm : j ≤ Fl.mm := KA.fl_m ▸ hj
    obtain ⟨L0, ⟨hmem, γ, hγ⟩, -⟩ := Y.Rep_ex j hjm a L hL
    have hL0 : (Fl.Pj j).IsLatTup L0 := Y.Rep_lat j (a, L0) hmem
    have hc : KA.cls j a L0 = KA.cls j a L :=
      (KA.cls_iff j hj a a L0 L hL0 hL).2 ⟨rfl, γ, hγ⟩
    have h0 := hT j h1 hj (a, L0) hmem
    rw [← hc, h0, hγ, Formalism.L2.G.Pend.card_stab_smul (Lv.lev j a) γ L0]
    rfl

theorem stabilizer_all_instances : TieStabAllInst := by
  intro D ex cc u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hU hS hR j hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    exact stabilizer_base_instance D ex cc u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y KA.cls hU hS
  · exact (stabilizer_restrict_iff D ex cc u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y).1 hR j hpos hj

end Formalism.L2.KerInert.KernelStabilizer
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.KernelStabilizer

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def StabEqAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _),
    StabEqRest (CmpJ.kerAtMu_any K H hS Gt Ch hCh)

def TieStabAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ (CmpJ.kerAtMu_any K H hS Gt Ch hCh).cls j

theorem stabilizer_any_level : TieStabAny := by
  intro D c Tw u μ w h _ Fl Lv K I H hS Gt Ch hCh std vp unif eO eO_spec dG dG_spec om Y hU hS0 j hj
  exact stabilizer_all_instances D Tw c u μ w h Fl Lv Ch (CmpJ.kerAtMu_any K H hS Gt Ch hCh) std vp unif eO eO_spec dG dG_spec om Y
    hU hS0 K.stab_eq j hj

end Formalism.L2.KerInert.SecondKernelStabilizers
end
end

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

theorem tieStab_kaAtAny [Fact (D.what₂.places.resChar w).Prime] (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) (Ch : Chain Lv) (hCh)
    (std) (vp) (unif) (eO) (eO_spec) (dG) (dG_spec) (om) (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (hU : DV.Used D μ) (hS0 : OrbitPlaces.Stab0 D) (j : ℕ) (hj : j ≤ D.R.m) : TieStabAt (Y := Y) u μ (kaAtAny X H Gt Ch hCh).cls j :=
  Formalism.L2.KerInert.SecondKernelStabilizers.stabilizer_any_level D c Tw u μ w h Fl Lv (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt Ch hCh std vp unif eO
    eO_spec dG dG_spec om Y hU hS0 j hj

end Formalism.MainNotions.G.KAat

end
end
