module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.ProdFL
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.WhitStd
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.RgGu

theorem rank_piTensor_le_one {h : ℕ} (M : Fin h → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (hM : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  let b := fun a => Module.Free.chooseBasis ℂ (M a)
  have hs : ∀ a, Subsingleton (Module.Free.ChooseBasisIndex ℂ (M a)) := fun a =>
    Cardinal.le_one_iff_subsingleton.1 (by rw [(b a).mk_eq_rank'']; exact hM a)
  rw [← (Basis.piTensorProduct b).mk_eq_rank'', Cardinal.le_one_iff_subsingleton]
  infer_instance


set_option maxHeartbeats 800000 in
theorem whitRankStd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  intro k _ _ _ _ hW hI ψ hc h1 h N x hd
  have h2 : Module.rank ℂ (⨂[ℂ] a, TwJacquet (x a).rep (unipB k (Fin (x a).1)) (whitChar ψ (x a).1)) ≤ 1 :=
    rank_piTensor_le_one _ fun a => hI ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr
  obtain ⟨e⟩ := hW ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
    (fun a => (x a).2.rep.smooth)
  have h3 := e.rank_eq
  change Module.rank ℂ (TwJacquet (multiProd (stdBlocks (fun a => (x a).1) hd) (fun a => (x a).rep)) (unipB k (Fin N))
    (whitChar ψ N)) ≤ 1
  rw [h3]
  exact h2

end GlobalTheory.RgGu

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.RgGu

theorem whitRankIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankIrr k :=
  fun k _ _ _ _ => PositivityTheory.rg.gu.whit.whitRankIrr k

theorem whitRankStd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.WhitRankStd k :=
  fun k _ _ _ _ => whitRankStd_of_heredity k (GlobalTheory.T.whittaker_heredity k) (whitRankIrr k)

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.NuPair k :=
  fun k _ _ _ _ => GlobalTheory.RgGu.Nup2.nuPair k

end GlobalTheory.RgGu

end
