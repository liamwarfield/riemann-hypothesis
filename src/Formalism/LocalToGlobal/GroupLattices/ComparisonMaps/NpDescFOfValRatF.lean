module

public import Formalism.SharpRestriction.GrowthBounds.JointsLit
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
public import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescOfValRat
namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

variable {D : D7} (c : LatCmp D)

theorem yvRat (h : ValRat c) : Formalism.MainNotions.G.Joints.Lit.YvRat c :=
  fun u w hg v => yvRat_of_valRat c h u w hg v

theorem npDesc_of_valRat {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (h : ValRat c) : c.NPDesc X Y K :=
  Formalism.MainNotions.G.Joints.Lit.NPDesc_of c hT X Y K hv (yvRat c h)

end Formalism.L2.G.Cmp
end

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

def ValRatF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, ValRat (Fm.ex x hx i).cmp

theorem npDescF_of_valRatF {eps : ℝ} (Fm : FamP eps) (h : ValRatF Fm) : NPDescF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i hx1 => ?_⟩
  refine npDesc_of_valRat _ (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK ?_ (hx0 x hx i hx1)
  exact (Fm.ex x hx1 i).lat.vram

theorem CmpTied.valRat {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D}
    {c : LatCmp D} (K : CmpTied D X T Gt c) : ValRat c := by
  intro u w hg x i L hL
  exact ⟨_, ((K.tie u w hg).val_cmp x i L hL).symm⟩

end Formalism.L2.G.Cmp
