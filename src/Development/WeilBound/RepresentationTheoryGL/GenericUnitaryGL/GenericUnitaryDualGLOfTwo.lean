module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGLOfExhaustion

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedCommPole
noncomputable section

namespace GlobalTheory.RgGu.Unl

theorem lUnlinkedIrr_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  exact lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)
    PositivityTheory.Geo.geometricLemmaFiltration (PositivityTheory.RgGu.NR.nuPair k)

theorem lUnlinkedComm_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedComm k :=
  fun k _ _ _ _ => lUnlinkedComm_of_irr k (lUnlinkedIrr_pole hZ k)

end GlobalTheory.RgGu.Unl

end
end

noncomputable section

namespace GlobalTheory.RgGu.Holds

theorem genericUnlinkedGL_holds : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedIrr_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k :=
  GlobalTheory.RgGu.Unl.lUnlinkedIrr_pole PositivityTheory.RgGu.segmentRepresentation

theorem lUnlinkedComm_holds :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedComm k :=
  GlobalTheory.RgGu.Unl.lUnlinkedComm_pole PositivityTheory.RgGu.segmentRepresentation

end GlobalTheory.RgGu.Holds

end
