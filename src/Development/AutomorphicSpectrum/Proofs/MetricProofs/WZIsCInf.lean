module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffSheetIff
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffSheetIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem cInfAt_sheet_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (f : CxPts t τ → ℝ) (y : CxPts p σ), CInfAt f (sheet t τ y) ↔ CInfAt (fun z : CxPts p σ => f (sheet t τ z)) y := by
  intro k _ _ X p t τ σ f y
  have hE := (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  constructor
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, hE.continuous.continuousAt.eventually h₅⟩
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, ?_⟩
    show ∀ᶠ w in 𝓝 (sheet t τ y), f w = F fun a => ev t τ W (g a) w
    rw [← hE.map_nhds_eq, eventually_map]
    exact h₅

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffSheetIffStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_sheet_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (f : CxPts t τ → ℝ) (y : CxPts p σ), CInfAt f (sheet t τ y) ↔ CInfAt (fun z : CxPts p σ => f (sheet t τ z)) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.cInfAt_sheet_iff | exact GlobalTheory.CompanionTheory.Ar.BaseZ.cInfAt_sheet_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.cInfAt_sheet_iff <;> assumption)
end
end

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem wZ_isCInf : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf := by
  intro k _ _ X p t L τ i y hy
  have hy' : unsheet p y ∈ ptsIn p (emb p y) (L.B.U i) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  refine (GlobalTheory.T.contDiff_sheet_iff k X p t τ (emb p y) ((wZ L t τ).φ i) (unsheet p y)).2 ?_
  refine (L.cInf (emb p y) i _ hy').congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hy'] with z hz
  exact wOver_wZ L t τ _ i z hz

end GlobalTheory.CompanionTheory.Ar.BaseZ
