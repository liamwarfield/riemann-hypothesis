module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaVectorBundleAnySpace
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.N81
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.E4
public import Development.EtaleCohomology.EtaleSheaves.AwSpec
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.A0Alt

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafChartRing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

end LateralTheory.E.t_E6Cut
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Aff

structure RF where
  obj : ∀ (A : Type) [CommRing A], Type
  map : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → obj A → obj B
  map_id : ∀ {A : Type} [CommRing A] (x : obj A), map (RingHom.id A) x = x
  map_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (x : obj A),
    map (g.comp f) x = map g (map f x)
  rel : ∀ {A : Type} [CommRing A], obj A → obj A → Prop
  map_rel : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x y : obj A}, rel x y → rel (map f x) (map f y)

structure RF.Hom (X Y : RF) where
  app : ∀ (A : Type) [CommRing A], X.obj A → Y.obj A
  nat : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : X.obj A), app B (X.map f x) = Y.map f (app A x)

def RF.Hom.Rel {X Y : RF} (h : X.Hom Y) : Prop :=
  ∀ {A : Type} [CommRing A] {x y : X.obj A}, X.rel x y → Y.rel (h.app A x) (h.app A y)

def CN (X : RF) : Spc where
  obj n :=
    { obj := fun U => {x : Fin (n.unop.len + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}
      map := fun f => TypeCat.ofHom fun x =>
        ⟨fun i => X.map f.unop.appTop.hom (x.1 i), fun i j => X.map_rel _ (x.2 i j)⟩
      map_id := fun U => by
        ext x i
        exact X.map_id (x.1 i)
      map_comp := fun f g => by
        ext x i
        exact X.map_comp f.unop.appTop.hom g.unop.appTop.hom (x.1 i) }
  map θ :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => x.1 (θ.unop.toOrderHom i), fun i j => x.2 _ _⟩
      naturality := fun U V f => rfl }
  map_id n := rfl
  map_comp θ θ' := rfl

def CN.map {X Y : RF} (h : X.Hom Y) (hr : h.Rel) : CN X ⟶ CN Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => h.app _ (x.1 i), fun i j => hr (x.2 i j)⟩
      naturality := fun U V f => by
        refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext (funext fun i => ?_)
        exact h.nat f.unop.appTop.hom (x.1 i) }
  naturality n m θ := rfl

def RF.sub (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) : RF where
  obj A _ := {x : X.obj A // P x}
  map f x := ⟨X.map f x.1, hP f x.2⟩
  map_id x := Subtype.ext (X.map_id x.1)
  map_comp f g x := Subtype.ext (X.map_comp f g x.1)
  rel x y := X.rel x.1 y.1
  map_rel f _ _ h := X.map_rel f h

def RF.subι (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.sub P hP).Hom X where
  app _ _ x := x.1
  nat _ _ := rfl

theorem RF.subι_rel (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.subι P hP).Rel := fun h => h

variable (D : Type) [CommRing D]

def Vec (N : ℕ) : RF where
  obj A _ := {x : (D →+* A) × (Fin N → A) // Ideal.span (Set.range x.2) = ⊤}
  map f x := ⟨(f.comp x.1.1, f ∘ x.1.2), by rw [Set.range_comp, ← Ideal.map_span, x.2, Ideal.map_top]⟩
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel {A} _ x y := x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j
  map_rel {A B} _ _ f x y h := by
    obtain ⟨h1, u, h2⟩ := h
    refine ⟨congrArg f.comp h1, Units.map (f : A →* B) u, funext fun j => ?_⟩
    simp [h2]

variable {D}

def P2 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop :=
  Ideal.span (Set.range fun j : Fin d => x.1.2 j.castSucc) = ⊤

def P1 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop := IsUnit (x.1.2 (Fin.last d))

theorem second_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P2 x) :
    P2 ((Vec D (d + 1)).map f x) := by
  have : (Set.range fun j : Fin d => ((Vec D (d + 1)).map f x).1.2 j.castSucc) =
      f '' (Set.range fun j : Fin d => x.1.2 j.castSucc) := by
    rw [← Set.range_comp]; rfl
  rw [P2, this, ← Ideal.map_span, h, Ideal.map_top]

theorem first_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    P1 ((Vec D (d + 1)).map f x) := h.map f

variable (D)

abbrev L2 (d : ℕ) : RF := (Vec D (d + 1)).sub P2 second_property_map

abbrev L1 (d : ℕ) : RF := (Vec D (d + 1)).sub P1 first_property_map

def fstV (d : ℕ) : (L2 D d).Hom (Vec D d) where
  app _ _ x := ⟨(x.1.1.1, fun j => x.1.1.2 j.castSucc), x.2⟩
  nat _ _ := rfl

section Formal
open LateralTheory.E.t_E6Cut
variable {R : Type} [CommRing R] (F : Shv R)

end Formal

end UpperTheory.Aff

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.A0
namespace UpperTheory.Et.D2

theorem a0 : LateralTheory.E.EtaleChapterDTwo := LateralTheory.Fix.EtaleChapterDTwo.s57

theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDTwo := a0

end UpperTheory.Et.D2
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdLeafLocOfLeafLevel
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Et

structure SlopeTestRemainingChoices : Prop where
  sheaf : type_of% @GlobalTheory.T.etaleSheafSections_ext_and_glue
  resol : type_of% @GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
  freeS : type_of% @GlobalTheory.T.free_sections_ext_res_map
  evs : type_of% @GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties
  rep : type_of% @GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff
  sec : type_of% @GlobalTheory.T.degreeZeroSectionClass_properties
  aw : type_of% @GlobalTheory.T.cup_eq_class_of_isAW
  twist : type_of% @GlobalTheory.T.tateTwist_sections_locally_generated
  pair : type_of% @GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique
  unit : type_of% @GlobalTheory.T.tateTwistUnitClass_rootClass_spec

section Site
variable {C : Type 1} [Category.{0} C] {S : Type 1} [CommRing S]

abbrev PM (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] : Type 2 := Cᵒᵖ ⥤ ModuleCat.{1} S

structure Dat (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] (ι : Type) where
  P : ι → ℤ → PM C S
  dP : ∀ b s t, P b s ⟶ P b t
  Q : ℤ → PM C S
  dQ : ∀ s t, Q s ⟶ Q t
  e : ι → ℤ
  φ : ∀ b s, P b (s - e b) ⟶ Q s
  ddP : ∀ b s t u, dP b s t ≫ dP b t u = 0
  ddQ : ∀ s t u, dQ s t ≫ dQ t u = 0
  comm : ∀ b s t, s + 1 = t → φ b s ≫ dQ s t = dP b (s - e b) (t - e b) ≫ φ b t

variable {ι : Type} [Fintype ι] (D : Dat C S ι)

end Site

section Rep
variable {R : Type} [CommRing R]

def Rep {I : Cx R} {U : Scheme.{0}} {n : ℤ} (z : Sec (I.X n) U) (c : CohomologyClass ((chains R).obj (sch.obj U)) I n) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj U)) I n, CohomologyClass.mk α = c ∧ ev α.1 0 n (by simp) U (𝟙 U) = z

variable {S Y : Scheme.{0}} (p' : Y ⟶ S)

end Rep

section Classes
variable (q : ℕ) {S Y : Scheme.{0}} (p' : Y ⟶ S) {ι : Type} [Fintype ι] {e : ι → ℤ} {j : ℤ} (w : ∀ b, Ht q (sch.obj Y) (e b) j)

end Classes

end UpperTheory.Et

end
end

namespace UpperTheory.Et

theorem etale_duality_trace_isomorphism : GlobalTheory.EtC.D2 := D2.intersectionNumber_baseChange GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf GlobalTheory.T.etC_b3 GlobalTheory.T.integralSurjection_cechDescent_tateTwist GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one GlobalTheory.T.etale_cohomology_ind_etale_base_change GlobalTheory.T.homotopy_invariance_etale_alt GlobalTheory.T.etale_cohomology_locally_acyclic GlobalTheory.EtC.projectiveBundleFormula_vectorBundle_any_space

theorem integerApproximationCount_holds : GlobalTheory.EtC.D3 := D3.intersectionNumber_baseChange GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf GlobalTheory.T.etC_b3 GlobalTheory.T.integralSurjection_cechDescent_tateTwist GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one GlobalTheory.T.etale_cohomology_ind_etale_base_change GlobalTheory.T.homotopy_invariance_etale_alt GlobalTheory.T.etale_cohomology_locally_acyclic GlobalTheory.EtC.projectiveBundleFormula_vectorBundle_any_space etale_duality_trace_isomorphism

theorem etale_base_change_of_duality : GlobalTheory.EtC.E3 := E3.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf, GlobalTheory.T.integralSurjection_cechDescent_tateTwist, GlobalTheory.T.etale_cohomology_ind_etale_base_change, GlobalTheory.T.homotopy_invariance_etale_alt⟩

theorem etale_finiteness_of_duality : GlobalTheory.EtC.E4 := e4 GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf GlobalTheory.T.etC_b3 GlobalTheory.T.integralSurjection_cechDescent_tateTwist GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one GlobalTheory.T.etale_cohomology_ind_etale_base_change GlobalTheory.T.homotopy_invariance_etale_alt GlobalTheory.T.etale_cohomology_locally_acyclic GlobalTheory.EtC.projectiveBundleFormula_vectorBundle_any_space etale_duality_trace_isomorphism integerApproximationCount_holds affine_proper_base_change proper_base_change etale_base_change_of_duality

end UpperTheory.Et
