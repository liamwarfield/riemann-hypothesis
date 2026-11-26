module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitCuspOfSegCuspGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

@[expose] public section

namespace CompanionTheory.Exh

theorem lUnlinkedIrr_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : GlobalTheory.BZSeg.LUnlinkedIrr k :=
  GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible k irreducibleAdmissibleGL (GlobalTheory.T.segment_jacquet_all irreducibleAdmissibleGL hZ) (fun k _ _ _ _ => (geometricLemmaGL k).1)
    (GlobalTheory.CompanionTheory.BZNuPair.nuPair k irreducibleAdmissibleGL) (GlobalTheory.T.whittaker_rank_standard_of_heredity k (GlobalTheory.T.whittaker_heredity k) (CompanionTheory.rg.gu.whit.whitRankIrr k))
    fun _ _ x hd => GlobalTheory.T.product_irreducible_finite_length irreducibleAdmissibleGL x hd

end CompanionTheory.Exh
