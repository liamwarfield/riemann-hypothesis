module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

@[expose] public section

noncomputable section

namespace PositivityTheory.SphericalProduct

theorem jacquet_hecke (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : A2 G :=
  GlobalTheory.T.jacquet_projection_hecke_holds G

theorem iwahori_u : IwahoriU :=
  GlobalTheory.T.iwahori_unipotent_datum

theorem dom_u : DomU :=
  GlobalTheory.T.dominant_unipotent_contraction

end PositivityTheory.SphericalProduct

end
