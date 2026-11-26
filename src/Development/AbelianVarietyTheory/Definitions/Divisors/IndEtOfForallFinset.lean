module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import GroundTheory.AutomorphicForms.GKModules.Garding
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct

namespace GlobalTheory.EtC

abbrev AbCx : Type 2 := CochainComplex AddCommGrpCat.{1} ℤ

def SurjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (z : D.X n), D.d n (n + 1) z = 0 →
    ∃ (c : C.X n) (y : D.X (n - 1)), C.d n (n + 1) c = 0 ∧ ψ.f n c = z + D.d (n - 1) n y

def InjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (c : C.X n), C.d n (n + 1) c = 0 → (∃ y : D.X (n - 1), ψ.f n c = D.d (n - 1) n y) →
    ∃ b : C.X (n - 1), C.d (n - 1) n b = c

section Abstract
variable {T : Type 1} [Category.{0} T]

def WExact (M : T ⥤ AddCommGrpCat.{1}) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  Function.Injective (M.map (a.app ⦋0⦌)) ∧
  (∀ y : M.obj (X.obj ⦋0⦌), M.map (X.δ (n := 0) 0) y = M.map (X.δ (n := 0) 1) y → ∃ x : M.obj U, M.map (a.app ⦋0⦌) x = y) ∧
  ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1)

abbrev term (C : T ⥤ AbCx) (n : ℤ) : T ⥤ AddCommGrpCat.{1} := C ⋙ HomologicalComplex.eval _ _ n

def LocExact (Cov : MorphismProperty T) (C : T ⥤ AbCx) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n y = (C.map g).f n z

def LocSurj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X (n - 1)), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d (n - 1) n y

def LocInj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (c : (C.obj U).X n), (C.obj U).d n (n + 1) c = 0 →
    (∃ y : (D.obj U).X (n - 1), (φ.app U).f n c = (D.obj U).d (n - 1) n y) →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n b = (C.map g).f n c

def Refines (Cov : MorphismProperty T)
    (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop) : Prop :=
  ∀ (U V : T) (g : U ⟶ V), Cov g → ∃ (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (h : V ⟶ X.obj ⦋0⦌),
    g ≫ h = a.app ⦋0⦌ ∧ Q U X a

def lev (Ψ : T ⥤ PShᵒᵖ) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) :
    ((X ⋙ Ψ).leftOp : Spc) ⟶ disc.obj (Ψ.obj U).unop where
  app n := (Ψ.map (a.app n.unop)).unop
  naturality m n f := by
    have h : a.app n.unop ≫ X.map f.unop = a.app m.unop := (a.naturality f.unop).symm.trans (Category.id_comp _)
    change (Ψ.map (a.app n.unop) ≫ Ψ.map (X.map f.unop)).unop = (Ψ.map (a.app m.unop)).unop ≫ 𝟙 _
    rw [← Ψ.map_comp, h, Category.comp_id]

def coAug [HasFiniteWidePushouts T] {U V : T} (g : U ⟶ V) : (CosimplicialObject.const T).obj U ⟶ (Arrow.mk g).cechConerve :=
  (Arrow.mk g).augmentedCechConerve.hom

end Abstract

variable (R : Type) [CommRing R]

def HCK (I : Cx R) : (Cx R)ᵒᵖ ⥤ AbCx where
  obj K := HomComplex K.unop I
  map f :=
    { f := fun n => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun β : Cochain _ I n => (Cochain.ofHom f.unop).comp β (zero_add n))
        (fun _ _ => Cochain.comp_add _ _ _ _))
      comm' := fun i j _ => by
        ext β
        exact δ_ofHom_comp f.unop β j }
  map_id K := by
    ext n β
    exact Cochain.id_comp β
  map_comp f g := by
    ext n β
    change (Cochain.ofHom (g.unop ≫ f.unop)).comp β (zero_add n) =
      (Cochain.ofHom g.unop).comp ((Cochain.ofHom f.unop).comp β (zero_add n)) (zero_add n)
    rw [Cochain.ofHom_comp]
    exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

def HC (F : Shv R) : Spcᵒᵖ ⥤ AbCx := (chains R).op ⋙ HCK R (res R F)

def Hyp {T : Type 1} [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) {U : T} {X : CosimplicialObject T}
    (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, QuasiIso ((chains R).map (lev (Φ ⋙ ((evaluation _ PSh).obj k).op) a))


variable {R} in
def onRings (F : Shv R) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R) := Scheme.Spec.rightOp ⋙ F.obj


variable {R} in
def Finitary (F : Shv R) : Prop := PreservesFilteredColimitsOfSize.{0, 0} (onRings F)


variable {R} in
abbrev Sec.pull {F : Shv R} {U V : Scheme.{0}} (j : V ⟶ U) (x : Sec F U) : Sec F V := (F.obj.map j.op).hom x

def ContCone (F : Shv R) {I : Type} [SmallCategory I] [IsCofiltered I] {G : I ⥤ Spc} (c : Cone G) : Prop :=
  ∀ n : ℤ, (∀ x : H R c.pt F n, ∃ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = x) ∧
    ∀ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = 0 → ∃ (k : I) (f : k ⟶ i), pull R (G.map f) F n y = 0

def AcycF (E : Spc) (F : Shv R) : Prop := ∀ n : ℤ, 0 < n → Subsingleton (H R E F n)

def EtFF : MorphismProperty CommRingCat.{0} := fun _ _ g => g.hom.Etale ∧ g.hom.FaithfullyFlat

def IndEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O)

def IndFEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty fun f => f.Etale ∧ f.Finite) (CommRingCat.ofHom (algebraMap A O))

theorem indEt_of_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] : IndEt A O :=
  MorphismProperty.le_ind _ _ (RingHom.etale_algebraMap.2 inferInstance)

theorem indFEt_of_finite_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] [Module.Finite A O] :
    IndFEt A O :=
  MorphismProperty.le_ind _ _ ⟨RingHom.etale_algebraMap.2 inferInstance, RingHom.finite_algebraMap.2 inferInstance⟩

set_option synthInstance.maxHeartbeats 200000 in
def bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Over S ⥤ Spc where
  obj U := pullback p (sch.map U.hom)
  map {U V} g := pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← sch.map_comp, Over.w g])
  map_id U := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp [pullback.map]

set_option synthInstance.maxHeartbeats 200000 in
def bcMap {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) : bc (α ≫ p) ⟶ bc p where
  app U := pullback.map (α ≫ p) (sch.map U.hom) p (sch.map U.hom) α (𝟙 _) (𝟙 _) (by simp) (by simp)
  naturality U V g := by apply pullback.hom_ext <;> simp [bc, pullback.map]

def QcqsOver {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k),
    QuasiCompact r ∧ QuasiSeparated r ∧ e.hom ≫ p.app k = yoneda.map r

def IsStalk {S : Scheme.{0}} (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S) : Prop :=
  SH O ∧ ∃ (A : Type) (_ : CommRing A) (_ : Algebra A O) (j : Spec (CommRingCat.of A) ⟶ S), Etale j ∧ IndEt A O ∧
    s = Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j


variable {R} in
def Gen (F : Shv R) (S : Scheme.{0}) (g : Sec F S) : Prop :=
  ∀ (U : Scheme.{0}) (s : U ⟶ S),
    (∀ (x : Sec F U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (c : R), Etale j ∧ j v = u ∧
      Sec.pull j x = (ULift.up c : ULift.{1} R) • Sec.pull (j ≫ s) g) ∧
    ∀ c : R, Nonempty U → (ULift.up c : ULift.{1} R) • Sec.pull s g = 0 → c = 0


variable {R} in
def val {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) : Sec F U :=
  (s.hom.app (op U)).hom (freeGen R P U x)

def cechPt {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    Sx (cech f) k U :=
  (WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
    (fun i => by rw [← yoneda.map_comp, h i])).app (op U) (𝟙 U)


variable {R} in
def cobd {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (SimplicialObject.δ E i) ≫ s)


variable {R} in
def IsCls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n) : Prop :=
  ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
    z.1 = Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n


variable {R} in
def Z1 (F : Shv R) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : AddSubgroup ((onRings F).obj (CommRingCat.of (B ⊗[A] B))) :=
  AddMonoidHom.eqLocus
    ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom
    (((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom +
     ((onRings F).map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom)

def UCoc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Prop :=
  Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (u : B ⊗[A] B)

def descMod (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Submodule A B :=
  LinearMap.eqLocus ((LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale

structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t

structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U

end GlobalTheory.LogPair
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.LGrp

section Rational
open Polynomial

def IsLaurentPoly (R : RatFunc ℂ) : Prop :=
  ∃ (m : ℕ) (p : ℂ[X]), R * RatFunc.X ^ m = algebraMap _ _ p

def lFactor (S : Multiset ℂˣ) : RatFunc ℂ := (S.map fun a : ℂˣ => (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹).prod

end Rational

section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable [MeasurableSpace (GL n k)]

variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}

omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)


omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring

private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega


omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_eq_zpow (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]


end ZetaNonvanishing₂

end GlobalTheory.LGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

end GlobalTheory.LogPair
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
noncomputable section

open MeasureTheory GroundTheory.Automorphic

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)

structure SmFn [MeasurableSpace G] (μ : Measure G) (S : Submodule ℂ (G → ℂ)) (K : Set G)
    (Λ : List (Fin d) → (G → ℂ) → ℂ) : Prop where
  lin : ∀ l, ∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ l (c • f + f') = c * Λ l f + Λ l f'
  bdd : ∀ l, ∃ C : ℝ, ∀ f ∈ S, ‖Λ l f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ
  der : ∀ l i, ∀ f ∈ S, HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) (Λ (i :: l) f) 0

def solG (P : Polynomial ℂ) : Submodule ℂ (G → ℂ) :=
  (LinearMap.ker (Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P)).map
    (h.smoothFuns (F := ℂ)).subtype

theorem mem_solG {P : Polynomial ℂ} {f : G → ℂ} : f ∈ solG h b P ↔ ∃ hf : h.IsSmoothFun f,
    Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P
      (⟨f, hf⟩ : h.smoothFuns (F := ℂ)) = 0 := by
  simp only [solG, Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hf, h0⟩
    exact ⟨⟨f, hf⟩, h0, rfl⟩

namespace SmFnEx

end SmFnEx

end GlobalTheory.HCA

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerCounitAlgHomBaseChangeField
open TensorProduct

namespace GlobalTheory

theorem ker_counitAlgHom_baseChange_field (O B κ : Type) [CommRing O] [CommRing B] [Bialgebra O B]
    [Field κ] [Algebra O κ] :
    RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)) =
      Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B)
        (RingHom.ker (Bialgebra.counitAlgHom O B)) := by
  have hs : Function.Surjective (Bialgebra.counitAlgHom O B) := fun c =>
    ⟨algebraMap O B c, by simp⟩
  rw [← Algebra.TensorProduct.lTensor_ker _ hs]
  have key : ∀ x : κ ⊗[O] B, Bialgebra.counitAlgHom κ (κ ⊗[O] B) x =
      Algebra.TensorProduct.rid O κ κ
        (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O B) x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c b => simp [TensorProduct.counit_tmul]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, key, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem hopf_order_formula_fibre :
    (∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Module.finrank k A = Module.finrank k (A ⧸ Ideal.map (f : B →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k B))) * Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap)) → ∀ (O A B κ : Type) [CommRing O] [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B] [Module.Finite O A] [Field κ] [Algebra O κ] (f : B →ₐc[O] A), Module.finrank κ (TensorProduct O κ A) = Module.finrank κ (TensorProduct O κ (A ⧸ Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))) * Module.finrank κ (LinearMap.range ((f : B →ₐ[O] A).toLinearMap.baseChange κ)) := by
  intro H O A B κ _ _ _ _ _ _ _ _ f
  have h := H κ (κ ⊗[O] A) (κ ⊗[O] B) (Bialgebra.TensorProduct.map (BialgHom.id κ κ) f)
  have hI : Ideal.map ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B))) =
      Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A)
        (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B))) := by
    rw [ker_counitAlgHom_baseChange_field]
    refine (Ideal.map_map
      ((Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) : B →+* κ ⊗[O] B)
      ((((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)) : κ ⊗[O] B →+* κ ⊗[O] A)).trans ?_
    refine Eq.trans ?_ (Ideal.map_map ((f : B →ₐ[O] A) : B →+* A)
      ((Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) : A →+* κ ⊗[O] A)).symm
    congr 1
  have hL : ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A).toLinearMap =
      (f : B →ₐ[O] A).toLinearMap.baseChange κ := by
    ext b
    simp
  rw [hI, hL] at h
  rw [h, (Algebra.TensorProduct.tensorQuotientEquiv (R := O) κ A κ
    (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))).toLinearEquiv.finrank_eq]

end GlobalTheory
end

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module

namespace GlobalTheory.PDiv

theorem finrank_eq_ker_mul_range (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    finrank k A = finrank k (A ⧸ kerIdeal f) *
      finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  exact GlobalTheory.finrank_eq_mul_of_basis_tensor_self k (AlgHom.range (f : B →ₐ[k] A)) A _ Subtype.val_injective
    ⟨((Module.finBasis k _).baseChange A).map e.symm⟩

variable {O : Type} [CommRing O]

abbrev fibreDim (M : Type) [AddCommGroup M] [Module O M] (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] M)

abbrev fibreRank {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField))

section Linear

variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]

theorem fibreDim_congr (e : M ≃ₗ[O] N) (q : PrimeSpectrum O) : fibreDim M q = fibreDim N q :=
  (e.baseChange O _ M N).finrank_eq

theorem fibreRank_comp_of_surjective (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective _ hf)

theorem fibreRank_equiv_comp (e : N ≃ₗ[O] P) (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (e.toLinearMap ∘ₗ f) q = fibreRank f q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (e.baseChange O _ N P) _

variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]

theorem fibreDim_dual (q : PrimeSpectrum O) : fibreDim (CartierDual O M) q = fibreDim M q :=
  (fibreDim_congr (CartierDual.toDual O M) q).trans (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M M _ LinearMap.id).1

theorem rankAtStalk_dual (q : PrimeSpectrum O) :
    rankAtStalk (CartierDual O M) q = rankAtStalk M q := by
  rw [rankAtStalk_eq, rankAtStalk_eq]
  exact fibreDim_dual q

theorem fibreRank_transpose (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (CartierDual.transpose f) q = fibreRank f q := by
  have h : CartierDual.transpose f = (CartierDual.toDual O M).symm.toLinearMap ∘ₗ
      (f.dualMap ∘ₗ (CartierDual.toDual O N).toLinearMap) := rfl
  rw [h, fibreRank_equiv_comp, fibreRank_comp_of_surjective _ (CartierDual.toDual O N).surjective]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M N _ f).2

end Linear

variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]

theorem fibreDim_eq_ker_mul_range (f : B →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreRank (f : B →ₐ[O] A).toLinearMap q :=
  GlobalTheory.hopf_order_formula_fibre finrank_eq_ker_mul_range O A B _ f

theorem fibreDim_ne_zero (q : PrimeSpectrum O) : fibreDim A q ≠ 0 := by
  have : Nontrivial (q.asIdeal.ResidueField ⊗[O] A) :=
    (counitAlgHom q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] A)).domain_nontrivial
  exact finrank_pos.ne'

variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]

theorem dual_map_surjective (f : B →ₐc[O] A)
    (h : ∀ q : PrimeSpectrum O, fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreDim B q) :
    Function.Surjective (CartierDual.map f) := by
  refine (GlobalTheory.surjective_injective_of_fibre_rank O _ _ (CartierDual.transpose (f : B →ₐ[O] A).toLinearMap)).1 fun q => ?_
  refine (fibreRank_transpose _ q).trans (Eq.trans ?_ (fibreDim_dual q).symm)
  have h1 := fibreDim_eq_ker_mul_range f q
  have h2 : fibreDim (A ⧸ kerIdeal f) q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, zero_mul])
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) (h1.symm.trans (h q))

theorem fibreDim_ker_dual [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by
  have h1 := fibreDim_eq_ker_mul_range g q
  have h2 := fibreDim_eq_ker_mul_range (CartierDual.map g) q
  have h3 : fibreRank (CartierDual.map g : CartierDual O A →ₐ[O] CartierDual O A).toLinearMap q =
    fibreRank (g : A →ₐ[O] A).toLinearMap q := fibreRank_transpose (g : A →ₐ[O] A).toLinearMap q
  rw [h3, fibreDim_dual, h1] at h2
  have h4 : fibreRank (g : A →ₐ[O] A).toLinearMap q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, mul_zero])
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4) h2).symm

theorem ker_eq_of_fibreDim_eq {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by
  refine le_antisymm (fun d hd => ?_) hI
  let π' : (D ⧸ I) →ₐ[O] E := Ideal.Quotient.liftₐ I π hI
  have hs : Function.Surjective π' := fun e => by
    obtain ⟨d, rfl⟩ := hπ e
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  have hi := (GlobalTheory.surjective_injective_of_fibre_rank O _ _ π'.toLinearMap).2 inferInstance inferInstance hs h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hi (a₁ := Ideal.Quotient.mk I d) (a₂ := 0)
    (by rw [map_zero]; exact hd))

end GlobalTheory.PDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ProdFam
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]


open Classical in
def idxSign (τ : κ → ι) (S : Finset κ) : ℤ := (-1) ^ ((S ×ˢ S).filter fun x => x.1 < x.2 ∧ τ x.2 < τ x.1).card


open Classical in
def pullIdx (τ : κ → ι) (a : Finset ι → E) : Finset κ → E := fun S =>
  if Set.InjOn τ (S : Set κ) then idxSign τ S • a (S.image τ) else 0

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def fstL : ι ×ₗ κ → ι := fun x => (ofLex x).1

def sndL : ι ×ₗ κ → κ := fun x => (ofLex x).2

def crossC {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') :
    Finset (ι ×ₗ κ) → E'' := fun u =>
  ∑ j ∈ u, μ (pullIdx fstL a (u.filter (· ≤ j))) (pullIdx sndL b (u.filter (j ≤ ·)))

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
end
end
