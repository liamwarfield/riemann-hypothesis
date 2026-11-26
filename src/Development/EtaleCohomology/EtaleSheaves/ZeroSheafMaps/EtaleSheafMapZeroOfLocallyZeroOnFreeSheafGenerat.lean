module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShMapZeroPf
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem Cov.trans {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y : B.Etale⦄ ⦃f : Y ⟶ U⦄, S f → Sieve Y := fun Y f hf =>
    Classical.choose (hPQ Y f (hP Y f hf))
  refine ⟨Sieve.bind S R, (EtTop B).bind_covering hS
    (fun Y f hf => (Classical.choose_spec (hPQ Y f (hP Y f hf))).1), ?_⟩
  rintro U'' _ ⟨Y, g, f, hf, hg, rfl⟩
  exact (Classical.choose_spec (hPQ Y f (hP Y f hf))).2 U'' g hg

def EtaleLift' : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K : DerivedCategory (SShv B q)) (U : B.Etale)
  (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶
    (DerivedCategory.homologyFunctor (SShv B q) 0).obj K),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ K,
    (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x)

def LeafGen : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (H H' : SShv B q) (g : H ⟶ H'),
  (∀ (U : B.Etale) (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶ H),
    Cov U (fun U' a => (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s ≫ g = 0)) → g = 0

theorem zero_of (hA : EtaleLift') (hB : LeafGen) (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q))
    (f : K ⟶ K')
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ K), Cov U (fun U' a => (OU B q).map a ≫ x ≫ f = 0)) :
    (DerivedCategory.homologyFunctor (SShv B q) 0).map f = 0 := by
  apply hB B q _ _ _
  intro U s
  refine Cov.trans (hA B q K U s) ?_
  rintro U' a ⟨x, hx⟩
  refine (h U' x).mono fun U'' b hb => ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of% hx, ← Functor.map_comp,
    ← Functor.map_comp, hb, Functor.map_zero]

theorem LeafShMapZero_of (hA : EtaleLift') (hB : LeafGen) : LeafShMapZero := by
  intro B q K K' f m h
  have h0 := zero_of hA hB B q _ _ ((shiftFunctor _ m).map f) h
  have e := (DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso_hom_naturality m (0 : ℤ) m (by simp) f
  have h0' : ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift (0 : ℤ)).map
      ((shiftFunctor _ m).map f) = 0 := h0
  change ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift m).map f = 0
  rw [← cancel_epi (((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso m (0 : ℤ) m (by simp)).hom.app K),
    comp_zero, ← e, h0', zero_comp]

end LateralTheory.E.LeafShMapZeroPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShMapZeroPf.Gen
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf

abbrev F0 (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ SShv B q :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q))) ⋙ presheafToSheaf (EtTop B) _

def e0 (B : Scheme.{0}) (q : ℕ) : OU B q ⋙ DerivedCategory.homologyFunctor (SShv B q) 0 ≅ F0 B q :=
  Functor.isoWhiskerLeft (F0 B q) (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0) ≪≫ Functor.rightUnitor _

def EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (H H' : SShv B q) (g : H ⟶ H'),
  (∀ (U : B.Etale) (t : (F0 B q).obj U ⟶ H), Cov U (fun U' a => (F0 B q).map a ≫ t ≫ g = 0)) → g = 0

theorem LeafGen_of (hG : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators) : LeafGen := by
  intro B q H H' g h
  apply hG B q H H' g
  intro U t
  refine (h U ((e0 B q).hom.app U ≫ t)).mono fun U' a ha => ?_
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  rw [← cancel_epi ((e0 B q).hom.app U'), comp_zero, ← Category.assoc, ← n, Category.assoc]
  exact ha

end LateralTheory.E.LeafShMapZeroPf.Gen
