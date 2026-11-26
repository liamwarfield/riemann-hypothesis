module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomology
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomology
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem finite_cechLB_homology (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB) (hv : VeryAmpleBy f H s)
    (p : ℕ) : Module.Finite R ((cechLB f M (fun i => nonzeroLocus (s i))).homology p) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ :=
    exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨φ, hφ⟩ := hφ 0
  have := finite_grCech_homology (Fin (m + 1)) R N 𝒩 hN 0 p
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ hφ
  let e : cechComplex (grCube (Fin (m + 1)) 𝒩 0) ≅ cechLB f M (fun i => nonzeroLocus (s i)) :=
    asIso (cechComplexMap φ) ≪≫ (cechLBTwZero f _ hM hH).symm
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso e p).toLinearEquiv

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomologyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cechLineBundle_homology : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ p, Module.Finite R ((cechLB f M (fun i => nonzeroLocus (s i))).homology p) := by
  first | exact @GlobalTheory.AbLaw.finite_cechLB_homology | exact GlobalTheory.AbLaw.finite_cechLB_homology | (intros; apply GlobalTheory.AbLaw.finite_cechLB_homology <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SerreVanishingH1Twist
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FirstCohomologyVanishesOfExactSecCube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem firstCohomologyVanishes_of_exact_secCube (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (hA : ∀ i, IsAffineOpen (D i))
    (h : Function.Exact (Cube.d (secCube f M D) 1) (Cube.d (secCube f M D) 2)) : FirstCohomologyVanishes M :=
  CechOne.h1Zero_of_exactAt_one f hM hc hA
    ((cechComplex_exactAt_succ_iff (secCube f M D) 0).2 h)

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SerreVanishingH1Twist
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_h1Zero_tw_of_veryAmpleBy (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB)
    (hs : VeryAmpleBy f H s) : ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ := GlobalTheory.T.exists_finite_gradedModule_lineBundleSections R Y f H m s M hH hM hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hN
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hφ t
  have := isIso_cechComplexMap φ hφ
  have h1 := (cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2)
  have h2 := h1.of_iso (asIso (cechComplexMap φ))
  exact firstCohomologyVanishes_of_exact_secCube R Y f (tw M H t) (Fin (m + 1)) (fun i => nonzeroLocus (s i))
    (isLB_tw hM hH t) hs.1 (fun i => (hs.2 i).1) ((cechComplex_exactAt_succ_iff _ 0).1 h2)

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SerreVanishingH1TwistStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_h1_twist : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t) := by
  first | exact @GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy | exact GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy | (intros; apply GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy <;> assumption)
end
end
