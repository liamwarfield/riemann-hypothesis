module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomology
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem cechLB_homology_finite_of_affine_cover : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → IsSeparated f → IsProjBy f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite R ((cechLB f M D).homology n) := by
  intro R _ Y f _ M κ _ _ D hM hsep hproj hD hcov n
  obtain ⟨H, hH, m, s, hs⟩ := hproj
  have hfin := GlobalTheory.T.finite_cechLineBundle_homology R Y f H m s M hH hM hs n
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers R Y f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) κ D hM hsep
    (fun i => (hs.2 i).1) hs.1 hD hcov n
  letI := hfin
  exact Module.Finite.equiv e

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCoverStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cechLB_homology_of_affine_cover : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → IsSeparated f → IsProjBy f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite R ((cechLB f M D).homology n) := by
  first | exact @GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover | exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover | (intros; apply GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem nonempty_perf_of_noetherian : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R], Flat f → IsProjBy f → ∀ M : LB Y, M.IsLB → Nonempty (Perf f M) := by
  intro R _ Y f _ hf ⟨H, hH, m, s, hs⟩ M hM
  have hD := (GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hs).2.2
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0}
      (cechLB f M (fun i => nonzeroLocus (s i))) (m + 1)
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD) (GlobalTheory.T.finite_cechLineBundle_homology R Y f H m s M hH hM hs)
  exact GlobalTheory.T.threeTermComplex_of_projective_cech_model R Y f M (Fin (m + 1)) _ K φ hM hs.1 hD ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherianStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R], Flat f → IsProjBy f → ∀ M : LB Y, M.IsLB → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.AbLaw.nonempty_perf_of_noetherian | exact GlobalTheory.AbLaw.nonempty_perf_of_noetherian | (intros; apply GlobalTheory.AbLaw.nonempty_perf_of_noetherian <;> assumption)
end
end
