module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]

structure Model (A : Over (Sp K)) where
  Y : Over (Sp R)
  e : (Over.pullback (spMap (algebraMap R K))).obj Y ≅ A
  smooth : Smooth Y.hom
  sep : IsSeparated Y.hom
  qc : QuasiCompact Y.hom
variable {R} {A A' : Over (Sp K)}

def Model.j (M : Model R A) : A.left ⟶ M.Y.left := M.e.inv.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))

def Model.twist (M : Model R A) (f : A ≅ A') : Model R A' := ⟨M.Y, M.e ≪≫ f, M.smooth, M.sep, M.qc⟩

def Model.prod (M : Model R A) (N : Model R A') : Model R (A ⊗ A') where
  Y := M.Y ⊗ N.Y
  e := (Functor.Monoidal.μIso (Over.pullback (spMap (algebraMap R K))) M.Y N.Y).symm ≪≫ tensorIso M.e N.e
  smooth := by have := M.smooth; have := N.smooth; show Smooth (pullback.fst _ _ ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; have := N.sep; show IsSeparated (pullback.fst _ _ ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; have := N.qc; show QuasiCompact (pullback.fst _ _ ≫ M.Y.hom); infer_instance

def Model.sp [IsLocalRing R] (M : Model R A) : Set M.Y.left := {y | M.Y.hom y = IsLocalRing.closedPoint R}

def Model.Irr [IsLocalRing R] (M : Model R A) : Prop := IsIrreducible M.sp

def Extends (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left) : Prop :=
  g ≫ N.Y.hom = U.ι ≫ M.Y.hom ∧ (M.j ∣_ U) ≫ g = (M.j ⁻¹ᵁ U).ι ≫ f.left ≫ N.j

def DefAt (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) : Prop :=
  ∃ (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left), y ∈ U ∧ Extends M N f U g

def IsoAt (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) : Prop :=
  ∃ (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left), y ∈ U ∧ Extends M N f U g ∧ IsOpenImmersion g

def GenIso [IsLocalRing R] (M : Model R A) (N : Model R A') (f : A ⟶ A') : Prop := ∃ y ∈ M.sp, IsoAt M N f y

def Model.Le (M N : Model R A) : Prop := ∃ g : M.Y ⟶ N.Y, IsOpenImmersion g.left ∧ M.j ≫ g.left = N.j

def Compat (M N : Model R A) : Prop :=
  ∃ (W : Model R A) (g : W.Y ⟶ M.Y) (h : W.Y ⟶ N.Y), IsOpenImmersion g.left ∧ IsOpenImmersion h.left ∧
    W.j ≫ g.left = M.j ∧ W.j ≫ h.left = N.j ∧ IsClosedImmersion (lift g h).left

def WeakNeron [IsLocalRing R] {I : Type} (M : I → Model R A) : Prop :=
  ∀ (R' K' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'], (IsLocalRing.maximalIdeal R).map (algebraMap R R') = IsLocalRing.maximalIdeal R' →
    ∀ a : Sp K' ⟶ A.left, a ≫ A.hom ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) →
      ∃ (i : I) (b : Sp R' ⟶ (M i).Y.left), b ≫ (M i).Y.hom = spMap (algebraMap R R') ∧ spMap (algebraMap R' K') ≫ b = a ≫ (M i).j

def cstK (A : Over (Sp K)) (U : A.left.Opens) : K →+* Γ(A.left, U) :=
  (A.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

structure VF (A : Over (Sp K)) where
  D : ∀ U : A.left.Opens, Γ(A.left, U) →+ Γ(A.left, U)
  leibniz : ∀ U a b, D U (a * b) = a * D U b + b * D U a
  const : ∀ U c, D U (cstK A U c) = 0
  res : ∀ (U V : A.left.Opens) (h : V ≤ U) a,
    D V ((A.left.presheaf.map (homOfLE h).op).hom a) = (A.left.presheaf.map (homOfLE h).op).hom (D U a)

def jac {I : Type} [Fintype I] [DecidableEq I] (D : I → VF A) (U : A.left.Opens) (t : I → Γ(A.left, U)) : Γ(A.left, U) :=
  (Matrix.of fun i j => (D i).D U (t j)).det

def IsFrame {I : Type} [Fintype I] [DecidableEq I] (D : I → VF A) : Prop :=
  SmoothOfRelativeDimension (Fintype.card I) A.hom ∧ ∀ x : A.left, ∃ (U : A.left.Opens) (t : I → Γ(A.left, U)), x ∈ U ∧ IsUnit (jac D U t)

def HasOrd [IsLocalRing R] {I : Type} [Fintype I] [DecidableEq I] (M : Model R A) (D : I → VF A) (π : R) (n : ℤ) : Prop :=
  (∀ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), ∃ s : Γ(M.Y.left, U),
    jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s) ∧
  ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) (s : Γ(M.Y.left, U)), ((U : Set M.Y.left) ∩ M.sp).Nonempty ∧ IsUnit s ∧
    jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s
section
variable [GrpObj A] [IsCommMonObj A]

def transl (a : 𝟙_ (Over (Sp K)) ⟶ A) : A ≅ A where
  hom := (toUnit A ≫ a) * 𝟙 A
  inv := (toUnit A ≫ a)⁻¹ * 𝟙 A
  hom_inv_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc]
  inv_hom_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc]

def shear (A : Over (Sp K)) [GrpObj A] : Bool → (A ⊗ A ⟶ A ⊗ A)
  | true => lift (fst A A) (fst A A * snd A A)
  | false => lift (fst A A) ((fst A A)⁻¹ * snd A A)

def BirLaw [IsLocalRing R] (M : Model R A) : Prop :=
  M.Irr ∧ (∀ b, GenIso (M.prod M) (M.prod M) (shear A b)) ∧ GenIso M M (ι[A])

def Strict [IsLocalRing R] (M : Model R A) : Prop :=
  BirLaw M ∧ ∀ b, ∀ x ∈ M.sp,
    (∃ z, (fst M.Y M.Y).left z = x ∧ IsoAt (M.prod M) (M.prod M) (shear A b) z) ∧
    ∃ z, (snd M.Y M.Y).left z = x ∧ IsoAt (M.prod M) (M.prod M) (shear A b) z
end

def SH (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] : Prop :=
  IsDiscreteValuationRing R ∧ HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) ∧ IsFractionRing R K

def SmConn {S : Scheme.{0}} (G : Over S) [GrpObj G] : Prop :=
  IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧ GeometricallyConnected G.hom

def Wt {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens)
    (u : Γ(G.left, V)) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u

def GoodOpen {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Prop :=
  IsAffineOpen V ∧ (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V ∧
    ∃ u : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, Wt i V (u (Multiplicative.ofAdd χ)).val χ

def IsQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom i ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ SmConn B

def polyPt {S : Scheme.{0}} {G Z : Over S} [GrpObj G] (F : End G) (P : Polynomial ℤ) (x : Z ⟶ G) : Z ⟶ G :=
  ((List.range (P.natDegree + 1)).map fun n => (x ≫ (F ^ n).asHom) ^ P.coeff n).prod

def Defect {R B R' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (π : R) (c : ℕ) : Prop :=
  letI := a.toRingHom.toAlgebra
  ∀ w ∈ Submodule.torsion R' (TensorProduct B R' (KaehlerDifferential R B)), algebraMap R R' π ^ c • w = 0

def Unr {R : Type} [CommRing R] (π : R) (R' : Type) [CommRing R'] [Algebra R R'] : Prop :=
  ∃ _ : IsDomain R', IsDiscreteValuationRing R' ∧ Irreducible (algebraMap R R' π)

def Model.ofAlgebra (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] :
    Model R ((Over.pullback (spMap (algebraMap R K))).obj (Over.mk (spMap (algebraMap R B)))) where
  Y := Over.mk (spMap (algebraMap R B))
  e := Iso.refl _
  smooth := by
    show Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  sep := by show IsSeparated (Spec.map _); infer_instance
  qc := by show QuasiCompact (Spec.map _); infer_instance

theorem Model.j_hom (M : Model R A) : M.j ≫ M.Y.hom = A.hom ≫ spMap (algebraMap R K) := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w M.e.inv

theorem extends_id (M : Model R A) (U : M.Y.left.Opens) : Extends M M (𝟙 A) U U.ι := by
  refine ⟨rfl, ?_⟩
  rw [morphismRestrict_ι, Over.id_left, Category.id_comp]

theorem isoAt_id (M : Model R A) (y : M.Y.left) : IsoAt M M (𝟙 A) y := ⟨⊤, (⊤ : M.Y.left.Opens).ι, trivial, extends_id M ⊤, inferInstance⟩

theorem IsoAt.defAt {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} (h : IsoAt M N f y) :
    DefAt M N f y := by
  obtain ⟨U, g, hy, he, -⟩ := h
  exact ⟨U, g, hy, he⟩

theorem Model.le_refl (M : Model R A) : M.Le M := ⟨𝟙 _, by rw [Over.id_left]; infer_instance, by rw [Over.id_left, Category.comp_id]⟩

theorem Model.Le.trans {M N P : Model R A} (h : M.Le N) (h' : N.Le P) : M.Le P := by
  obtain ⟨g, hg, hgj⟩ := h
  obtain ⟨g', hg', hgj'⟩ := h'
  refine ⟨g ≫ g', ?_, ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, ← Category.assoc, hgj, hgj']

def VF.zero (A : Over (Sp K)) : VF A where
  D _ := 0
  leibniz _ _ _ := by simp
  const _ _ := rfl
  res _ _ _ _ := by simp

section LocDer
variable {k B : Type} [CommRing k] [CommRing B] [Algebra k B] (d : Derivation k B B) (S : Submonoid B)

end LocDer

section SpecVF
variable {B : Type} [CommRing B] [Algebra K B]

end SpecVF

end GlobalTheory.SS
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZJ

abbrev OO (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) := (Valued.v : Valuation (PadicAlgCl p) NNReal).valuationSubring

abbrev cPt (p : ℕ) [Fact p.Prime] : Sp (OO p) := IsLocalRing.closedPoint (OO p)

abbrev gPt (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) ⟶ Sp (OO p) := spMap (OO p).subtype

abbrev kb (p : ℕ) [Fact p.Prime] : Type := IsLocalRing.ResidueField (OO p)

abbrev rPt (p : ℕ) [Fact p.Prime] : Sp (kb p) ⟶ Sp (OO p) := spMap (IsLocalRing.residue (OO p))

structure Core where
  Z : Scheme.{0}
  [integral : IsIntegral Z]
  π : Z ⟶ Sp ℤ
  flat : Flat π
  lft : LocallyOfFiniteType π
  qc : QuasiCompact π
  sep : IsSeparated π
  normal : IsNormalScheme Z
  U : Z.Opens
  ne : (U : Set Z).Nonempty
  g : ℕ
  A : Over U.toScheme
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  P : Over Z
  [intP : IsIntegral P.left]
  proper : IsProper P.hom
  G : P.left.Opens
  a : A.left ⟶ G.toScheme
  cart : IsPullback (a ≫ G.ι) A.hom P.hom U.ι
  e : Z ⟶ G.toScheme
  e_sec : e ≫ G.ι ≫ P.hom = 𝟙 Z
  e_zero : U.ι ≫ e = (eSec A ≫ a : U.toScheme ⟶ G.toScheme)

attribute [instance] Core.integral Core.grp Core.comm Core.intP

namespace Core

variable (C : Core)

abbrev GG : Over C.Z := Over.mk (C.G.ι ≫ C.P.hom)

def Cl {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) : Prop := Set.range (gPt p ≫ y) ⊆ C.U

structure Test {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  complete : IsAdicComplete (IsLocalRing.maximalIdeal V) V
  j : V →+* OO p
  j_inj : Function.Injective j
  j_loc : IsLocalHom j
  y₀ : Sp V ⟶ C.Z
  fac : spMap j ≫ y₀ = y
  H : Over (Sp V)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]
  smooth : SmoothOfRelativeDimension C.g H.hom
  sep : IsSeparated H.hom
  qc : QuasiCompact H.hom
  split : ∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj H)
  f : H.left ⟶ C.G.toScheme
  f_over : f ≫ C.GG.hom = H.hom ≫ y₀
  yK : Sp (FractionRing V) ⟶ C.U.toScheme
  yK_fac : yK ≫ C.U.ι = Out.jK V ≫ y₀
  φ : pullback H.hom (Out.jK V) ⟶ C.A.left
  φ_cart : IsGrpPullback ((Over.pullback (Out.jK V)).obj H) C.A yK φ
  φ_f : φ ≫ C.a = pullback.fst H.hom (Out.jK V) ≫ f
  imm : ∀ h : pullback H.hom (rPt p ≫ spMap j) ⟶ pullback C.GG.hom (rPt p ≫ y),
    h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h
  lift : ∀ b : Sp (OO p) ⟶ C.G.toScheme, b ≫ C.GG.hom = y →
    ∃ c : Sp (OO p) ⟶ H.left, c ≫ H.hom = spMap j ∧ c ≫ f = b

attribute [instance] Test.ring Test.dom Test.dvr Test.grp Test.comm

def HasTests : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), C.Cl y → Nonempty (C.Test y)

def Indep : Prop := ∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' →
  rPt p ≫ y = rPt p ≫ y' → ∀ b : Sp (OO p) ⟶ C.G.toScheme, b ≫ C.GG.hom = y →
  ∃ b' : Sp (OO p) ⟶ C.G.toScheme, b' ≫ C.GG.hom = y' ∧ rPt p ≫ b' = rPt p ≫ b

def Fib : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (x : Sp (kb p) ⟶ C.G.toScheme),
  x ≫ C.GG.hom = rPt p ≫ y → ∃ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j ∧ c ≫ τ.f = x

def Coord (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)) : Prop :=
  IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) =
    Ideal.span (Set.range fun i => (C.G.toScheme.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (C.Z.presheaf.stalk (C.GG.hom w))).map (C.GG.hom.stalkMap w).hom).radical

def TestCart : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y),
  IsPullback τ.f τ.H.hom C.GG.hom τ.y₀

def FibLaw : Prop := ∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (τ' : C.Test y')
  (K : Type) [Field K] [IsAlgClosed K] (r : Sp K ⟶ Sp τ.V) (r' : Sp K ⟶ Sp τ'.V),
  Set.range r = {IsLocalRing.closedPoint τ.V} → Set.range r' = {IsLocalRing.closedPoint τ'.V} →
  r ≫ τ.y₀ = r' ≫ τ'.y₀ → ∀ (c d : Over.mk r ⟶ τ.H) (c' d' : Over.mk r' ⟶ τ'.H),
  c.left ≫ τ.f = c'.left ≫ τ'.f → d.left ≫ τ.f = d'.left ≫ τ'.f →
  (c * d).left ≫ τ.f = (c' * d').left ≫ τ'.f ∧ (c⁻¹).left ≫ τ.f = (c'⁻¹).left ≫ τ'.f

structure Law where
  [grp : GrpObj C.GG]
  [comm : IsCommMonObj C.GG]
  smooth : SmoothOfRelativeDimension C.g C.GG.hom
  zero : (eSec C.GG : C.Z ⟶ C.G.toScheme) = C.e
  pull : IsGrpPullback C.A C.GG C.U.ι C.a
  test : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), IsGrpPullback τ.H C.GG τ.y₀ τ.f

end Core

theorem isNormalScheme_sp (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := by
  intro x
  refine ⟨inferInstance, ?_⟩
  have : (PrimeSpectrum.asIdeal x).IsPrime := PrimeSpectrum.isPrime x
  have h := StructureSheaf.IsLocalization.to_stalk R x
  exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk x) _ _ (_) _ _
    (PrimeSpectrum.asIdeal x).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h

def Core.zero (U : (Sp ℤ).Opens) (hU : (U : Set (Sp ℤ)).Nonempty) : Core where
  Z := Sp ℤ
  π := 𝟙 _
  flat := inferInstance
  lft := inferInstance
  qc := inferInstance
  sep := inferInstance
  normal := isNormalScheme_sp ℤ
  U := U
  ne := hU
  g := 0
  A := 𝟙_ (Over U.toScheme)
  ab :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (𝟙 U.toScheme))
      proper := inferInstanceAs (IsProper (𝟙 U.toScheme))
      geomConnected := by
        change GeometricallyConnected (𝟙 U.toScheme)
        infer_instance }
  dim := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 U.toScheme))
  P := 𝟙_ (Over (Sp ℤ))
  intP := inferInstanceAs (IsIntegral (Sp ℤ))
  proper := inferInstanceAs (IsProper (𝟙 (Sp ℤ)))
  G := ⊤
  a := U.ι ≫ (Sp ℤ).topIso.inv
  cart := by
    change IsPullback ((U.ι ≫ (Sp ℤ).topIso.inv) ≫ (⊤ : (Sp ℤ).Opens).ι) (𝟙 U.toScheme) (𝟙 (Sp ℤ)) U.ι
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  e := (Sp ℤ).topIso.inv
  e_sec := by
    change (Sp ℤ).topIso.inv ≫ (⊤ : (Sp ℤ).Opens).ι ≫ 𝟙 (Sp ℤ) = _
    simp
  e_zero := by
    change _ = 𝟙 U.toScheme ≫ U.ι ≫ (Sp ℤ).topIso.inv
    simp

end GlobalTheory.ZJ
end
end
