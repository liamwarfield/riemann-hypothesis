module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.JoinLinked

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0')
    (Φ : ∀ F : (∀ u, Formalism.L2.Forms.Forms0 D u), ∀ P : GlobalTheory.Mem.SRe.SPack D F, GlobalTheory.Mem.SRe.SRest P → Formalism.L2.Theta.GA D (D.sp.Y 0) → ℝ → Prop)
    {P' : GlobalTheory.Mem.SRe.SPack D F0'} {S' : GlobalTheory.Mem.SRe.SRest P'} {t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)} {c c' : ℝ}
    {P : GlobalTheory.Mem.SRe.SPack D F0} {S : GlobalTheory.Mem.SRe.SRest P} (hP : HEq P P') (hS : HEq S S') (ht : HEq t t') (hc : c = c')
    (h : Φ F0' P' S' t' c') : Φ F0 P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq ht
  subst hc
  exact h

theorem schurAll (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) :
    Formalism.IndefR.Links.SchurAll D :=
  fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2

section IndefiniteRowSideFullHecke

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

end IndefiniteRowSideFullHecke

section Wit

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.SRe

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}


end Wit

section Constructions₂

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

end Constructions₂

end GlobalTheory.Fc.JoinLinked

end
