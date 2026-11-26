module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.FirstChernClassLaws
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh (inter inter_le_comp)

namespace UpperTheory.Gal.DifferentialFormSections

variable {K : Type} [CommRing K]

abbrev Fm (K A : Type) [CommRing K] [CommRing A] [Algebra K A] : Type := ExteriorAlgebra A Ω[A⁄K]

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

def fmMap (φ : A →ₐ[K] B) : Fm K A →ₐ[K] Fm K B :=
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  (ExteriorAlgebra.lift A ⟨((ExteriorAlgebra.ι B).restrictScalars A) ∘ₗ KaehlerDifferential.map K K A B,
    fun _ => ExteriorAlgebra.ι_sq_zero _⟩).restrictScalars K

end

abbrev Sch (K : Type) [CommRing K] : Type 1 := Over (Spec (CommRingCat.of K))

def Sec (X : Sch K) (U : X.left.Opens) : Type := Γ(X.left, U)

instance (X : Sch K) (U : X.left.Opens) : CommRing (Sec X U) := inferInstanceAs (CommRing Γ(X.left, U))

instance (X : Sch K) (U : X.left.Opens) : Algebra K (Sec X U) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Hom.appLE X.hom ⊤ U le_top).hom : K →+* Γ(X.left, U)).toAlgebra

def secMap {X Y : Sch K} (f : Y ⟶ X) {U : X.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) : Sec X U →ₐ[K] Sec Y V where
  toRingHom := (Scheme.Hom.appLE f.left U V h).hom
  commutes' r := by
    have e : Scheme.Hom.appLE X.hom ⊤ U le_top ≫ Scheme.Hom.appLE f.left U V h = Scheme.Hom.appLE Y.hom ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE f.left X.hom ⊤ U V le_top h).trans ?_
      have e2 := Over.w f
      revert e2
      generalize Y.hom = g
      rintro rfl
      rfl
    exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r)) e

def secRes (X : Sch K) {U V : X.left.Opens} (h : V ≤ U) : Sec X U →ₐ[K] Sec X V := secMap (𝟙 X) h

variable {X Y : Sch K} {ι κ : Type}

abbrev cap (U : ι → X.left.Opens) {n : ℕ} (i : Fin n → ι) : X.left.Opens := inter (X := X.left.toTopCat) U i

abbrev Co (U : ι → X.left.Opens) (n : ℕ) : Type := ∀ i : Fin (n + 1) → ι, Fm K (Sec X (cap U i))

def dC (U : ι → X.left.Opens) (n : ℕ) : Co U n →ₗ[K] Co U (n + 1) :=
  LinearMap.pi fun i => ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    ((fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i k.succAbove))).toLinearMap ∘ₗ LinearMap.proj (i ∘ k.succAbove))

def Bd (U : ι → X.left.Opens) : (n : ℕ) → Submodule K (Co U n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dC U n)

abbrev HC (U : ι → X.left.Opens) (n : ℕ) : Type := LinearMap.ker (dC U n) ⧸ (Bd U n).submoduleOf (LinearMap.ker (dC U n))


abbrev all (X : Sch K) : X.left.affineOpens → X.left.Opens := Subtype.val

abbrev H (X : Sch K) (n : ℕ) : Type := HC (all X) n

structure IsCov (U : ι → X.left.Opens) : Prop where
  aff : ∀ i, IsAffineOpen (U i)
  cov : iSup U = ⊤

structure Coc (X : Sch K) : Type 1 where
  ι : Type
  U : ι → X.left.Opens
  cov : IsCov U
  g : ∀ i : Fin 2 → ι, (Sec X (cap U i))ˣ
  coc : ∀ i : Fin 3 → ι,
    secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 2)) (g (i ∘ Fin.succAbove 2)).val *
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 0)) (g (i ∘ Fin.succAbove 0)).val =
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 1)) (g (i ∘ Fin.succAbove 1)).val

end UpperTheory.Gal.DifferentialFormSections
end
end

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh

namespace UpperTheory.Gal.DifferentialFormSections

structure IsDiv {K : Type} [CommRing K] {W E : Sch K} (i : E ⟶ W) (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)) : Prop where
  closed : IsClosedImmersion i.left
  ker : ∀ j, RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ L.U j))).toRingHom = Ideal.span {s j}
  nzd : ∀ j, s j ∈ nonZeroDivisors (Sec W (L.U j))
  rel : ∀ j : Fin 2 → L.ι, secRes W (inter_le (X := W.left.toTopCat) L.U j 0) (s (j 0)) =
    (L.g j).val * secRes W (inter_le (X := W.left.toTopCat) L.U j 1) (s (j 1))

end UpperTheory.Gal.DifferentialFormSections
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open FunctorialResolution.Blowup

namespace UpperTheory.Gal.KunnethLefschetz.G

variable {R : Type} [CommRing R]

def XX (Z : Sch R) : Sch R := Over.mk (pullback.fst Z.hom Z.hom ≫ Z.hom)

def p1 (Z : Sch R) : XX Z ⟶ Z := Over.homMk (pullback.fst Z.hom Z.hom) rfl

def p2 (Z : Sch R) : XX Z ⟶ Z := Over.homMk (pullback.snd Z.hom Z.hom) pullback.condition.symm

def dg (Z : Sch R) : Z ⟶ XX Z := Over.homMk (pullback.diagonal Z.hom) (by
  change pullback.diagonal Z.hom ≫ pullback.fst Z.hom Z.hom ≫ Z.hom = Z.hom
  rw [pullback.diagonal_fst_assoc])

def IsBl {Z W : Sch R} (π : W ⟶ XX Z) : Prop := IsBlowupAlongIdealSheaf π.left (dg Z).left.ker

def Ex {Z W : Sch R} (π : W ⟶ XX Z) : Sch R := Over.mk (pullback.fst π.left (dg Z).left ≫ W.hom)

def exI {Z W : Sch R} (π : W ⟶ XX Z) : Ex π ⟶ W := Over.homMk (pullback.fst π.left (dg Z).left) rfl

def exG {Z W : Sch R} (π : W ⟶ XX Z) : Ex π ⟶ Z := Over.homMk (pullback.snd π.left (dg Z).left) (by
  change pullback.snd π.left (dg Z).left ≫ Z.hom = pullback.fst π.left (dg Z).left ≫ W.hom
  rw [← Over.w (dg Z), ← pullback.condition_assoc, Over.w π])

def Coord (Z : Sch R) (U : Z.left.Opens) {D : ℕ} (u : Fin D → Sec Z U) : Prop :=
  IsAffineOpen U ∧ (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] Sec Z U).toRingHom.Etale

structure DChart (Z : Sch R) (D : ℕ) where
  U : Z.left.Opens
  u : Fin D → Sec Z U
  coord : Coord Z U u
  N : (XX Z).left.Opens
  aff : IsAffineOpen N
  h1 : N ≤ (p1 Z).left ⁻¹ᵁ U
  h2 : N ≤ (p2 Z).left ⁻¹ᵁ U
  ker : RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N))).toRingHom =
    Ideal.span (Set.range fun k => secMap (p2 Z) h2 (u k) - secMap (p1 Z) h1 (u k))

def DChart.s {Z : Sch R} {D : ℕ} (c : DChart Z D) (k : Fin D) : Sec (XX Z) c.N := secMap (p2 Z) c.h2 (c.u k) - secMap (p1 Z) c.h1 (c.u k)

structure BChart {X W : Sch R} (π : W ⟶ X) (N : X.left.Opens) {D : ℕ} (s : Fin D → Sec X N) where
  V : Fin D → W.left.Opens
  aff : ∀ j, IsAffineOpen (V j)
  le : ∀ j, V j ≤ π.left ⁻¹ᵁ N
  cov : iSup V = π.left ⁻¹ᵁ N
  y : ∀ j, Fin D → Sec W (V j)
  surj : ∀ j, Function.Surjective (MvPolynomial.eval₂Hom (secMap π (le j)).toRingHom (y j))
  ker : ∀ j, RingHom.ker (MvPolynomial.eval₂Hom (secMap π (le j)).toRingHom (y j)) =
    Ideal.span (insert (MvPolynomial.X j - 1) (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k))
  inter : ∀ j k, V j ⊓ V k = W.left.basicOpen (show Γ(W.left, V j) from y j k)
  nzd : ∀ j, secMap π (le j) (s j) ∈ nonZeroDivisors (Sec W (V j))

def CoordEx : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) [SmoothOfRelativeDimension D Z.hom] (z : Z.left),
  ∃ (U : Z.left.Opens) (u : Fin D → Sec Z U), z ∈ U ∧ Coord Z U u

def DChartEx : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) [IsSeparated Z.hom],
  (∀ (U : Z.left.Opens) (u : Fin D → Sec Z U), Coord Z U u → ∀ z ∈ U, ∃ c : DChart Z D, c.U = U ∧ HEq c.u u ∧ (dg Z).left z ∈ c.N) ∧
  ∀ (c : DChart Z D) (N' : (XX Z).left.Opens), IsAffineOpen N' → ∀ h : N' ≤ c.N,
    RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N'))).toRingHom = Ideal.span (Set.range fun k => secRes (XX Z) h (c.s k))

def DCoord : Prop := ∀ (R : Type) [CommRing R] (Z : Sch R) (D : ℕ) (c : DChart Z D),
  (MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s).Etale

def BChartEx : Prop := ∀ (R : Type) [CommRing R] {X W : Sch R} (π : W ⟶ X) (I : X.left.IdealSheafData), IsBlowupAlongIdealSheaf π.left I →
  ∀ (N : X.left.affineOpens) (D : ℕ) (A : Type) [CommRing A] (φ : MvPolynomial (Fin D) A →+* Sec X N.1), φ.Flat →
    (show Ideal (Sec X N.1) from I.ideal N) = Ideal.span (Set.range fun k => φ (MvPolynomial.X k)) →
    Nonempty (BChart π N.1 fun k => φ (MvPolynomial.X k))

def BlowUpChart₂ : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} [IsSeparated Z.hom] (π : W ⟶ XX Z), IsBl π → ∀ (D : ℕ) (c : DChart Z D),
  Nonempty (BChart π c.N c.s)

def BCoord : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} (π : W ⟶ XX Z) (D : ℕ) (c : DChart Z D) (b : BChart π c.N c.s) (j : Fin D),
  (MvPolynomial.eval₂Hom ((secMap π (b.le j)).comp (secMap (p1 Z) c.h1)).toRingHom
    (Function.update (b.y j) j (secMap π (b.le j) (c.s j)))).Etale

def BlowUpOff : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
  (π : W ⟶ XX Z), IsBl π → IsProper π.left ∧ IsClosedImmersion (exI π).left ∧
    ∀ U : (XX Z).left.Opens, (U : Set (XX Z).left) = (Set.range (dg Z).left)ᶜ →
      IsIso (π.left ∣_ U) ∧ ((π.left ⁻¹ᵁ U : W.left.Opens) : Set W.left) = (Set.range (exI π).left)ᶜ

def BlowUpSmooth : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (D : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension D Z.hom] (π : W ⟶ XX Z), IsBl π →
    SmoothOfRelativeDimension D (π ≫ p1 Z).left ∧ SmoothOfRelativeDimension (D + D) W.hom

def ExChart : Prop := ∀ (R : Type) [CommRing R] {Z W : Sch R} [IsSeparated Z.hom] (π : W ⟶ XX Z) (D : ℕ) (c : DChart Z D)
  (b : BChart π c.N c.s) (j : Fin D), IsAffineOpen ((dg Z).left ⁻¹ᵁ c.N) ∧ IsAffineOpen ((exI π).left ⁻¹ᵁ b.V j) ∧
    RingHom.ker (secMap (exI π) (le_refl ((exI π).left ⁻¹ᵁ b.V j))).toRingHom = Ideal.span {secMap π (b.le j) (c.s j)} ∧
    ∃ h : (exI π).left ⁻¹ᵁ b.V j ≤ (exG π).left ⁻¹ᵁ ((dg Z).left ⁻¹ᵁ c.N), Function.Bijective
      (MvPolynomial.eval₂Hom (secMap (exG π) h).toRingHom fun k : {k : Fin D // k ≠ j} => secMap (exI π) le_rfl (b.y j k))

def ExSmooth : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z), IsBl π →
    SmoothOfRelativeDimension d (exG π).left ∧ IsProper (exG π).left ∧ Surjective (exG π).left

def ExDiv : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (D : ℕ) [IsSeparated Z.hom]
  [SmoothOfRelativeDimension D Z.hom] (π : W ⟶ XX Z), IsBl π → ∃ (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)), IsDiv (exI π) L s

def ProjProd : Prop := ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (q : Y ⟶ Sp R), IsProjOver p →
  (IsProjOver q → IsProjOver (pullback.fst p q ≫ p)) ∧ (∀ i : Y ⟶ X, IsClosedImmersion i → IsProjOver (i ≫ p)) ∧ IsProper p

def BlowUpEmbedding : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {X W : Scheme.{0}} (p : X ⟶ Sp R), IsProjOver p →
  ∀ (I : X.IdealSheafData) (π : W ⟶ X), IsBlowupAlongIdealSheaf π I → ∃ (M : ℕ) (f : W ⟶ PSpace R M) (h : π ≫ p = f ≫ PSpace.str R M),
    IsClosedImmersion (pullback.lift π f h : W ⟶ pullback p (PSpace.str R M))

def BlowUpTop : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Sch R) (d : ℕ) [SmoothOfRelativeDimension (d + 1) Z.hom],
  IsProjOver Z.hom → ∃ (W : Sch R) (π : W ⟶ XX Z), IsBl π ∧ IsProjOver (XX Z).hom ∧ IsProjOver W.hom ∧ IsProjOver (Ex π).hom ∧
    SmoothOfRelativeDimension (d + 1 + (d + 1)) (XX Z).hom ∧ SmoothOfRelativeDimension (d + 1 + (d + 1)) W.hom ∧
    SmoothOfRelativeDimension (d + (d + 1)) (Ex π).hom

end UpperTheory.Gal.KunnethLefschetz.G
