module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

abbrev genPt (R : Type) [CommRing R] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))

structure QFGroup (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] where

  G : Over (Spec (CommRingCat.of R))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  flat : Flat G.hom
  quasiFinite : LocallyQuasiFinite G.hom
  separated : IsSeparated G.hom
  quasiCompact : QuasiCompact G.hom
  finPres : LocallyOfFinitePresentation G.hom

  pt : T →* (genPt R ⟶ G)
  pt_inj : ∀ s t (x y : Spec (CommRingCat.of (FractionRing R))), (pt s).left x = (pt t).left y → s = t
  pt_onto : ∀ g : G.left, (G.hom g).asIdeal = ⊥ → ∃ t x, (pt t).left x = g
  gen_reduced : IsReduced (pullback G.hom (genPt R).hom)

attribute [instance] QFGroup.grp QFGroup.comm

def valAt {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE U ⊤ h).hom s)

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def QFGroup.RegularAt (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left) : Prop :=
  ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
    valAt (Γ.pt t).left U h s = f t

def QFGroup.btSet (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Set (T → R) :=
  {f | ∀ t, ∀ g ∈ U, Γ.RegularAt (fun h => algebraMap R (FractionRing R) (f (t * h))) g}

def QFGroup.btOrder (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Subalgebra R (T → R) :=
  Algebra.adjoin R (Γ.btSet U)

structure QFGroup.IsFinOpenSub (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Prop where
  finite : IsFinite (U.ι ≫ Γ.G.hom)
  one : ∀ x, (η[Γ.G]).left x ∈ U
  mul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ.G), (∀ z, x.left z ∈ U) → (∀ z, y.left z ∈ U) →
    ∀ z, (x * y).left z ∈ U
  inv : ∀ (S : Over (Spec (CommRingCat.of R))) (x : S ⟶ Γ.G), (∀ z, x.left z ∈ U) → ∀ z, (x⁻¹).left z ∈ U

structure QFGroup.IsBaseChange {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (Γ : QFGroup R T)
    (φ : R →+* R') (F : Γ'.G.left ⟶ Γ.G.left) : Prop where
  cart : IsPullback F Γ'.G.hom Γ.G.hom (Spec.map (CommRingCat.ofHom φ))
  mul : ∀ (S : Over (Spec (CommRingCat.of R'))) (x y : S ⟶ Γ'.G)
    (x₀ y₀ : Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G),
    x₀.left = x.left ≫ F → y₀.left = y.left ≫ F → (x₀ * y₀).left = (x * y).left ≫ F
  pts : ∃ (B : Type) (_ : CommRing B) (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (σ : T → (Spec (CommRingCat.of B) ⟶ Γ.G.left)),
    Function.Injective j ∧ j.comp i = algebraMap R _ ∧ j'.comp i = (algebraMap R' _).comp φ ∧
    (∀ t, σ t ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom i)) ∧
    (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left) ∧
    ∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ F

structure QFGroup.IsTorsionAlong (Γ : QFGroup R T) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left) : Prop where
  isOver : i ≫ G.hom = Γ.G.hom ≫ x
  mul : ∀ (Y : Over (Spec (CommRingCat.of R))) (y z : Y ⟶ Γ.G) (y₀ z₀ : Over.mk (Y.hom ≫ x) ⟶ G),
    y₀.left = y.left ≫ i → z₀.left = z.left ≫ i → (y₀ * z₀).left = (y * z).left ≫ i
  inj : ∀ (Y : Over (Spec (CommRingCat.of R))) (y z : Y ⟶ Γ.G), y.left ≫ i = z.left ≫ i → y = z
  kernel : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ G),
    g ^ N = 1 ↔ ∃ y : Y ⟶ Γ.G, y.left ≫ i = g.left

structure QFGroup.IsEmb (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) : Prop where
  isOver : j ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = Γ.G.hom
  pt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))

def QFGroup.TranslatesCover (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A))
    (U : Γ.G.left.Opens) : Prop :=
  ∀ P : PrimeSpectrum A, ∃ (t : T) (g : Γ.G.left), g ∈ U ∧
    ∀ (f f' : A), (∀ h, (f' : T → R) h = (f : T → R) (t * h)) → (f ∈ P.asIdeal ↔ f' ∈ (j g).asIdeal)

end GlobalTheory.CompanionTheory.Ar.BT
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

abbrev epsAt (x : Spec (CommRingCat.of R) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)

def IsTanAt (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (v : epsAt x ⟶ G) : Prop :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left

def epsMul (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def dualMap (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

structure LieModel (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
    [Module R E] where

  pt : E → (epsAt x ⟶ G)
  tan : ∀ e, IsTanAt G x (pt e)
  inj : Function.Injective pt
  onto : ∀ v, IsTanAt G x v → ∃ e, pt e = v
  add : ∀ e e', pt (e + e') = pt e * pt e'
  smul : ∀ (c : R) e, (pt (c • e)).left = Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (pt e).left

def LieModel.IsDiffOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) (f : G ⟶ G) (A : E →ₗ[R] E) : Prop :=
  ∀ e, M.pt (A e) = M.pt e ≫ f

def LieModel.IsActOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End R E) : Prop :=
  ∀ a, M.IsDiffOf (act a) (ρ a)

def eigSp {E : Type} [AddCommGroup E] [Module R E] {O : Type} [CommRing O] (ρ : O →+* Module.End R E)
    (σ : O →+* R) : Submodule R E :=
  ⨅ a, LinearMap.ker (ρ a - σ a • LinearMap.id)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X := ξ (IsLocalRing.closedPoint Ω)

def Cpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type := {p : X // genPt ξ ⤳ p}

def genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : X.presheaf.stalk p.1 →+* Ω :=
  (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom

def regAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω := (genMap ξ p).range

def unitAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

structure IsCptGen (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop where
  bij : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom
  inj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL

section Base

variable {F : Type} [Field F]

def IsInt {n : ℕ} (R : Subring F) (Z : Matrix (Fin n) (Fin n) F) : Prop := ∀ a b, Z a b ∈ R

theorem isInt_mul' (O : Subring F) {a : ℕ} {x y : Matrix (Fin a) (Fin a) F} (hx : IsInt O x)
    (hy : IsInt O y) : IsInt O (x * y) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => O.mul_mem (hx a k) (hy k b)

def GLint (O : Subring F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | IsInt O (g : Matrix (Fin a) (Fin a) F) ∧
    IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h, O.one_mem, O.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using isInt_mul' O hx hy, ?_⟩
    simpa [_root_.mul_inv_rev] using isInt_mul' O hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩

instance instMeasGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    MeasurableSpace (GL (Fin n) K) := borel _
instance instBorelGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    BorelSpace (GL (Fin n) K) := ⟨rfl⟩

def omegaS {a : ℕ} {m : Type} [Fintype m] (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin a) F)
    (Φ : Matrix m (Fin a) F → ℂ) : Matrix m (Fin a) F → ℂ :=
  fun x => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card m : ℝ) / 2) : ℝ) : ℂ) *
    Φ (x * (g : Matrix (Fin a) (Fin a) F))

end Base

section Local

variable {F : Type} [Field F]

def chi0 (δ : Fˣ →* ℂˣ) (x : F) : ℂ :=
  open Classical in if h : x = 0 then 0 else ((δ (Units.mk0 x h) : ℂˣ) : ℂ)

def bAA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin r) F :=
  x.submatrix (Fin.castAdd d) (Fin.castAdd c)
def bAD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin c) F :=
  x.submatrix (Fin.castAdd d) (Fin.natAdd r)
def bDA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin r) F :=
  x.submatrix (Fin.natAdd r) (Fin.castAdd c)
def bDD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin c) F :=
  x.submatrix (Fin.natAdd r) (Fin.natAdd r)

variable (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ)

def IsSphFn {c : ℕ} (χ : Fin c → F → ℂ) (φ : GL (Fin c) F → ℂ) : Prop :=
  ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
    φ (b * k) = ∏ i : Fin c, χ i ((b : Matrix (Fin c) (Fin c) F) i i) *
      ((nrm ((b : Matrix (Fin c) (Fin c) F) i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)

variable [TopologicalSpace F] [IsTopologicalRing F]

end Local

section More

variable {F : Type} [Field F]

def Mint (O : Subring F) (c : ℕ) : Set (GL (Fin c) F) := {g | IsInt O (g : Matrix (Fin c) (Fin c) F)}

def pEl {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) : GL (Fin (r + c)) F where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F))
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks ((m₁⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
      (-(((m₁⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B * ((m₂⁻¹ : GL (Fin c) F) : Matrix (Fin c) (Fin c) F))) 0
      ((m₂⁻¹ : GL (Fin c) F) : Matrix (Fin c) (Fin c) F))
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_neg,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      neg_add_cancel, neg_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.neg_mul,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      add_neg_cancel, neg_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def UnrChar (nrm : AbsoluteValue F ℝ) (q : ℕ) {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ) : Prop :=
  (∀ i, α i ≠ 0) ∧ ∀ i (x : F) (e : ℤ), nrm x = (q : ℝ) ^ (-e) → χ i x = α i ^ e

structure LF [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (q : ℕ) : Prop where
  O_eq : O = 𝒪[F]
  ne : ϖ ≠ 0
  lt_one : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ O, x = ϖ * o
  card : q = Nat.card 𝓀[F]
  nrm_unit : ∀ x : F, ValuativeRel.valuation F x = 1 → nrm x = 1
  nrm_pi : nrm ϖ = (q : ℝ)⁻¹

end More

end GlobalTheory.CompanionTheory.QL
end
end
