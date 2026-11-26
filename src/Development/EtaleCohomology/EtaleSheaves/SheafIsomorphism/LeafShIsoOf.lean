module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves

theorem Cov.bind {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' (a : U' ⟶ U), P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : Sieve U :=
    { arrows := fun Z c => ∀ (W : B.Etale) (d : W ⟶ Z), Q W (d ≫ c)
      downward_closed := fun {Z Z'} c hc e W d => by simpa [Category.assoc] using hc W (d ≫ e) }
  refine ⟨R, (EtTop B).transitive hS R ?_, fun U' a ha => by simpa using ha U' (𝟙 _)⟩
  intro Y f hf
  obtain ⟨S', hS', hQ⟩ := hPQ Y f (hP Y f hf)
  refine (EtTop B).superset_covering ?_ hS'
  intro Z c hc W d
  simpa [Category.assoc] using hQ W (d ≫ c) (S'.downward_closed hc d)

abbrev H0 (B : Scheme.{0}) (q : ℕ) := DerivedCategory.homologyFunctor (SShv B q) 0

def EtaleDerivedDegreeZeroHomologyLocallyLifts : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (t : (H0 B q).obj ((OU B q).obj U) ⟶ (H0 B q).obj M),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ M, (H0 B q).map ((OU B q).map a) ≫ t = (H0 B q).map x)

def EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (x : (OU B q).obj U ⟶ M), (H0 B q).map x = 0 → Cov U (fun U' a => (OU B q).map a ≫ x = 0)

def LeafSheafIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (F G : SShv B q) (g : F ⟶ G),
  (∀ (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F), t ≫ g = 0 →
    Cov U (fun U' a => (H0 B q).map ((OU B q).map a) ≫ t = 0)) →
  (∀ (U : B.Etale) (s : (H0 B q).obj ((OU B q).obj U) ⟶ G),
    Cov U (fun U' a => ∃ t : (H0 B q).obj ((OU B q).obj U') ⟶ F, (H0 B q).map ((OU B q).map a) ≫ s = t ≫ g)) →
  IsIso g

theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hS : LeafSheafIso) : LeafShIso := by
  intro B q L K ℓ m hinj hsurj
  set f := (shiftFunctor (DerivedCategory (SShv B q)) m).map ℓ with hf
  have key : IsIso ((H0 B q).map f) := by
    apply hS
    · intro U t ht
      refine Cov.bind (hL B q _ U t) ?_
      rintro U' a ⟨x, hx⟩
      have h1 : (H0 B q).map (x ≫ f) = 0 := by
        rw [Functor.map_comp, ← hx, Category.assoc, ht, comp_zero]
      have h2 := hinj U' x 0 ((hK B q _ U' _ h1).mono (fun U'' b hb => by simpa using hb))
      refine h2.mono (fun U'' b hb => ?_)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hx, ← Functor.map_comp, hb, comp_zero,
        Functor.map_zero]
    · intro U s
      refine Cov.bind (hL B q _ U s) ?_
      rintro U' a ⟨y, hy⟩
      refine (hsurj U' y).mono (fun U'' b ⟨x, hx⟩ => ⟨(H0 B q).map x, ?_⟩)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hy, ← Functor.map_comp, hx, Functor.map_comp]
  have e := ((H0 B q).isoShift m)
  exact (NatIso.isIso_map_iff e ℓ).1 key

end LateralTheory.E.LeafShIsoPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafSheafIsoOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf.Sh
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

def LeafSecRep : Prop := ∀ (B : Scheme.{0}) (q : ℕ), ∃ e : ∀ (F : SShv B q) (U : B.Etale),
    ((H0 B q).obj ((OU B q).obj U) ⟶ F) ≃ ToType (F.obj.obj (op U)),
  (∀ (F G : SShv B q) (g : F ⟶ G) (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : SShv B q) (U U' : B.Etale) (a : U' ⟶ U) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F),
    e F U' ((H0 B q).map ((OU B q).map a) ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : SShv B q) (U : B.Etale) (t t' : (H0 B q).obj ((OU B q).obj U) ⟶ F), e F U (t - t') = e F U t - e F U t')

theorem LeafSheafIso_of (hR : LeafSecRep) : LeafSheafIso := by
  intro B q F G g hinj hsurj
  obtain ⟨e, hg, hres, hsub⟩ := hR B q
  have h0 : ∀ (F : SShv B q) U, e F U 0 = 0 := fun F U => by simpa using hsub F U 0 0
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  refine (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · let t := (e F X.unop).symm x - (e F X.unop).symm y
    have ht : t ≫ g = 0 := by
      apply (e G X.unop).injective
      rw [hg, hsub, h0, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      simpa [sub_eq_zero] using hxy
    obtain ⟨S, hS, hP⟩ := hinj X.unop t ht
    refine (EtTop B).superset_covering ?_ hS
    intro U' a ha
    have := congrArg (e F U') (hP U' a ha)
    rw [hres, h0, hsub, Equiv.apply_symm_apply, Equiv.apply_symm_apply, map_sub, sub_eq_zero] at this
    exact this
  · obtain ⟨S, hS, hP⟩ := hsurj U ((e G U).symm s)
    refine (EtTop B).superset_covering ?_ hS
    intro U' a ha
    obtain ⟨t, ht⟩ := hP U' a ha
    refine ⟨e F U' t, ?_⟩
    rw [← hg, ← ht, hres, Equiv.apply_symm_apply]

end LateralTheory.E.LeafShIsoPf.Sh
end
end

namespace LateralTheory.E.LeafShIsoPf.Glue
open LateralTheory.E.LeafDegCut LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hR : LeafSecRep) : LeafShIso :=
  LateralTheory.E.LeafShIsoPf.LeafShIso_of hL hK (LeafSheafIso_of hR)

end LateralTheory.E.LeafShIsoPf.Glue
