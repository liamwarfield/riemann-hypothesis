module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) {a : XGeo D}

def LocX.Red {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) (x : S.P.J)
    (g : GL (Fin D.R.r) (kP PP)) : Prop :=
  ∀ (i j : Fin D.R.k ⊕ Fin (l.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ j → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val i j - (ofSplit l.q).pr (z : D.host.E)) < 1

structure SymRead (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k) : Prop where
  char : ∀ PP, (ofSplit (l PP).q).IsChar (pk W).ψ (S PP).ψ
  mu : ∀ PP j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ ((S PP).μ j)
  grp : ∀ g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1), g ∈ (lvP W).H ↔ ∀ PP, ∃ x, (l PP).Red (S PP) x (g PP)
  chr : ∀ (g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1)) (hg : g ∈ (lvP W).H) (x : ∀ PP, (S PP).P.J),
    (∀ PP, (l PP).Red (S PP) (x PP) (g PP)) → (lvP W).chi ⟨g, hg⟩ = ∏ PP, (S PP).P.lam (x PP)

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def PrimTop {c : Comm D} (tP : Finset (GlobalTheory.FinPl.Pl D)) (ζ₀ : Fin c.Lz.rank → D.host.E) : Prop :=
  ∀ p, p ∉ tP → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = p),
    a • ratV (vecB (c.oT D.R.m rfl) ζ₀) ∈ GlobalTheory.FinPl.latV (c.X D.R.m) (c.x D.R.m).L (· = p) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = p)

end GlobalTheory.MiTop

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

open GlobalTheory.ChainOnto (Com)

variable {D : D7}

section Common

variable {c : Comm D} {v : VCom c}

def Red (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure LocAt (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) : Prop where
  idem : Formalism.L2.NTheta.IsIdemAt G.q.e PP
  under : G.q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  frame : ∀ a (ha : 0 + a = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) 0 ≃ Fin (c.V 0).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 a ha).β * ((G.S.T (Fin D.R.t)).bas 0 a ha).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 a ha (e.symm i))

structure Bot (cm : Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) : Prop where
  com : cm.Is
  psi : cm.ψ = c.ψ
  mem : st.st.Is cm 0
  fin : b ∈ GfC (c.V 0)
  typ : IsTypePlaces cm.Pg
  loc : ∀ PP : cm.Pg, LocAt (G PP) PP.1 b st.β
  grp : ∀ g : ∀ PP : cm.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ cm.P.H ↔ ∀ PP, ∃ x, Red (G PP) PP.1 x (g PP)
  chr : ∀ (g : cm.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, Red (G PP) PP.1 (x PP) (g.1 PP)) →
    cm.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)

end Common

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

variable {W : RealPack ex} {u : D.what₂.Word}



end GlobalTheory.LevZero

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
noncomputable section
open Formalism.BasicNotions GlobalTheory.SeeSaw GlobalTheory.QPl
namespace GlobalTheory.QTw
variable {D : D7} {c : Comm D} {t : Tup c}

def resc (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * (s (j + 1) γ)⁻¹) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

def QPinU (v : VCom c) (w : VTup t) : Prop :=
  ∃ (w₀ : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ QPin v w₀ ∧ w = resc w₀ s

end GlobalTheory.QTw
end
end
