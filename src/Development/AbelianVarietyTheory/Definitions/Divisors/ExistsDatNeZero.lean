module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev Pt (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type := SpAlg R D ⟶ X

abbrev Fn0 (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → D

abbrev Fn1 (X : Over (Sp R)) : Type 1 :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D → D'

abbrev Fn2 (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → Pt X D → D

section Basic

variable {X : Over (Sp R)} {K : Type}

def Sm (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Prop :=
  ∃ i, ⊤ ≤ x.left ⁻¹ᵁ W i


variable (X) in
def whole : Unit → X.left.Opens := fun _ ↦ ⊤

theorem sm_whole {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Sm (whole X) x := ⟨(), fun _ _ ↦ trivial⟩

def IsCoc (W : K → X.left.Opens) (f : Fn1 X) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D'']
    [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'') (x : Pt X D), Sm W x →
    f D D'' (ψ.comp φ) x = ψ (f D D' φ x) + f D' D'' ψ (spOver φ ≫ x)

def IsCob (W : K → X.left.Opens) (f : Fn1 X) (k : Fn0 X) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
    Sm W x → f D D' φ x = k D' (spOver φ ≫ x) - φ (k D x)

def Fn1.neg (f : Fn1 X) : Fn1 X := fun D _ _ D' _ _ φ x ↦ -f D D' φ x

def Fn1.add (f f' : Fn1 X) : Fn1 X := fun D _ _ D' _ _ φ x ↦ f D D' φ x + f' D D' φ x

def Cohom (W : K → X.left.Opens) (f f' : Fn1 X) : Prop := ∃ k : Fn0 X, IsCob W (f.add f'.neg) k

def Fn1.zero (X : Over (Sp R)) : Fn1 X := fun _ _ _ _ _ _ _ _ ↦ 0

theorem Pt.w {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) :
    x.left ≫ X.hom ≫ 𝟙 _ = spMap (algebraMap R D) := by
  rw [Category.comp_id]; exact Over.w x

abbrev trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Thick (dp0 R) (X.hom ≫ 𝟙 _) :=
  Thick.triv D x.left x.w

def trivMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    trivAt x ⟶ trivAt (spOver φ ≫ x) := Thick.trivHom φ rfl

def fv (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) : Fn1 X := fun _ _ _ _ _ _ φ x ↦ ev f (trivMap φ x)


open Classical in
def evU {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) : D :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then evalAt x U h a else 0

def dl {D : Type} [CommRing D] (u : DualNumber D) : D := u.snd * Ring.inverse u.fst

def epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    DualNumber D →ₐ[R] DualNumber D' :=
  DualNumber.lift ⟨((TrivSqZeroExt.inlAlgHom R D' D').comp φ, DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ ↦ Commute.all _ _⟩

end Basic

section Group

variable {A : Over (Sp R)} [GrpObj A] {K : Type}

def IsAdd (f : Fn1 A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x y : Pt A D),
    g D' (spOver φ ≫ x) (spOver φ ≫ y) - φ (g D x y) = f D D' φ (x * y) - f D D' φ x - f D D' φ y

def IsSymCoc (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D],
    (∀ x y : Pt A D, g D x y = g D y x) ∧
    ∀ x y z : Pt A D, g D y z - g D (x * y) z + g D x (y * z) - g D x y = 0

def chi (n : ℕ) (g : Fn2 A) : Fn0 A := fun D _ _ x ↦ ∑ i ∈ Finset.range n, g D (x ^ i) x

end Group

section Cot

variable (R) (D : Type) [CommRing D] [Bialgebra R D]

@[reducible] def cotOp : Module Rᵐᵒᵖ (Cot R D) := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

attribute [local instance] cotOp

theorem cotCentral : IsCentralScalar R (Cot R D) := ⟨fun _ _ ↦ rfl⟩

theorem cotTower : IsScalarTower R Rᵐᵒᵖ (Cot R D) := ⟨fun r s m ↦ by
  change (r • s).unop • m = r • s.unop • m
  rw [MulOpposite.unop_smul, smul_eq_mul, mul_smul]⟩

attribute [local instance] cotCentral cotTower

abbrev cotExt : SqExt R := SqExt.ofModule R R (Cot R D)

def cotPt : D →ₐ[R] (cotExt R D).C :=
  AlgHom.ofLinearMap
    (Algebra.linearMap R (TrivSqZeroExt R (Cot R D)) ∘ₗ Coalgebra.counit +
      TrivSqZeroExt.inrHom R (Cot R D) ∘ₗ AugCot.d (Bialgebra.counitAlgHom R D))
    (by
      have h : AugCot.d (Bialgebra.counitAlgHom R D) 1 = 0 := by
        simpa using AugCot.d_algebraMap (Bialgebra.counitAlgHom R D) 1
      simp [h])
    (fun x y ↦ by
      have h := AugCot.d_mul (Bialgebra.counitAlgHom R D) x y
      ext
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · simp [TrivSqZeroExt.algebraMap_eq_inl, h, add_comm])

def cotSnd : (cotExt R D).C →ₗ[R] Cot R D := TrivSqZeroExt.sndHom R (Cot R D)


variable {R D} in
def cotVal {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (y : Pt X D) : Cot R D :=
  let y' : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  cotSnd R D ((cotExt R D).val y'.left y'.w f - fv f D (cotExt R D).C (cotPt R D) y)

end Cot

section Can

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

structure Dat (t : G.TorsionTower A) (c : primDR A) : Type 1 where

  f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))
  cl : H1.mk _ f = c.1

  g : Fn2 A
  add : IsAdd (fv f) g

  h : ∀ n, G.A n
  res : ∀ n, fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)) = h n - G.res n (h (n + 1))

variable {t : G.TorsionTower A} {c : primDR A} (d : Dat t c)

def Dat.coc (n : ℕ) : G.A n ⊗[R] G.A n :=
  d.g (G.A n ⊗[R] G.A n) (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
      (spOver Algebra.TensorProduct.includeRight ≫ t.y n) -
    (fv d.f (G.A n) (G.A n ⊗[R] G.A n) (Bialgebra.comulAlgHom R (G.A n)) (t.y n) -
      fv d.f (G.A n) (G.A n ⊗[R] G.A n) Algebra.TensorProduct.includeLeft (t.y n) -
      fv d.f (G.A n) (G.A n ⊗[R] G.A n) Algebra.TensorProduct.includeRight (t.y n)) -
    cobOne R (G.A n) (d.h n)

def Dat.om (n : ℕ) : Cot R (G.A n) :=
  cotVal d.f (t.y n) - dUnit (R := R) (d.h n)


variable (t c) in
def IsCan (x : G.RigExt) : Prop :=
  ∃ (d : Dat t c) (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ (∀ n, w.1 n = d.om n) ∧ x = G.rigMk (z, w)

def Dat.zero (t : G.TorsionTower A) : Dat t 0 where
  f := 0
  cl := map_zero _
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by
    change (0 : _) - φ 0 = 0 - 0 - 0
    simp
  h := 0
  res := fun n ↦ by
    change (0 : _) = 0 - G.res n 0
    simp

end Can

section Contract

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def ptV (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Pt (A ⊗ B) (DualNumber D) :=
  lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) (spOver (EpsWeil.epsMap R D) ≫ v)


variable (B) in
def pt0 {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Pt (A ⊗ B) D := lift x 1

def chartsA (P : LB (A ⊗ B).left) : P.ι → A.left.Opens := fun i ↦ (AbDual.inl A B).left ⁻¹ᵁ P.U i

def IsChoice (P : LB (A ⊗ B).left) (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), Sm (chartsA P) x → ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j D x)

def tanCoc (P : LB (A ⊗ B).left) (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι) (v : epsR R ⟶ B) :
    Fn1 A := fun D _ _ D' _ _ φ x ↦
  let x' : Pt A D' := spOver φ ≫ x
  dl (evU (ptV v x').left (P.U (j D' x') ⊓ P.U (j D x)) (P.g (j D' x') (j D x)).val)

def sndPull (u : Fn1 (A ⊗ B)) (v : epsR R ⟶ B) : Fn1 A := fun D _ _ D' _ _ φ x ↦
  (u (DualNumber D) (DualNumber D') (epsHom φ) (ptV v x)).snd

abbrev epsExt (R D : Type) [CommRing R] [CommRing D] [Algebra R D] : SqExt R := SqExt.ofModule R D D


variable (B) in
abbrev thickAt {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) :=
  (epsExt R D).thick (pt0 B x).left (pt0 B x).w

def IsContr (z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))) (v : epsR R ⟶ B) (κ : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
    (s' : trivAt (pt0 B (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x))
    (i' : trivAt (ptV v (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x))
    (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x)))
    (b : trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x))) (τ : thickAt B x ⟶ thickAt B (spOver φ ≫ x)),
    (∀ r, s.φ r = TrivSqZeroExt.inl r) → (∀ r, i.φ r = r) → (∀ r, s'.φ r = TrivSqZeroExt.inl r) → (∀ r, i'.φ r = r) →
    (∀ r, a.φ r = φ r) → (∀ r, b.φ r = epsHom φ r) → (∀ r, τ.φ r = epsHom φ r) →
    κ D D' φ x = TrivSqZeroExt.snd (R := D') (M := D')
      (z _ _ _ s τ - z _ _ _ a s' - z _ _ _ i τ + z _ _ _ b i')

end Contract

section Cube

variable {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {L : RigLB H}

end Cube

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

def IsBiRig {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def IsPPol {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  IsBiRig A P ∧ RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧
    ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1

def IsComplAt {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (ψ : A →+* R) : Prop :=
  IsNoetherianRing R ∧ IsAdicComplete (maximalIdeal R) R ∧ ψ.Flat ∧ ((maximalIdeal R).comap ψ).map ψ = maximalIdeal R ∧
    ∀ r : R, ∃ a b : A, IsUnit (ψ b) ∧ r * ψ b - ψ a ∈ maximalIdeal R

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (iw : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ)

def DataFrom (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (β : Q.B.left ⟶ T.B.left) (β₂ : (G2 Q.B).left ⟶ (G2 T.B).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ T.B T.M.L).pull β₂)),
    IsGrpPullback Q.B T.B (spMap iw) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap iw ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap iw) z J)

def DegFrom (D : DegPre V) (e : D.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (Q : Data V) (e' : D.X ≃+ Q.X), Refines Q (RingHom.id V) D e' ∧ DataFrom T iw s ε n Q (e'.symm.trans e)

end From

structure LowBase {o : Type} [CommRing o] (ζ : o) (n : ℕ) where

  h : ℕ

  F : SFam h n ζ

  W : Type
  [ring : CommRing W]
  [loc : IsLocalRing W]
  noeth : IsNoetherianRing W
  complete : IsAdicComplete (maximalIdeal W) W

  T : TautBase o W

  u : Sp W ⟶ (LowChart.powA F T.r).left
  u_et : IsEtaleCompletion (Scheme.stalkClosedPointTo u).hom
  u_sep : ((residue W).comp (Scheme.stalkClosedPointTo u).hom).FormallyUnramified
  u_base : u ≫ LowChart.toO F T.r = spMap T.b
  dim : T.g = h

  β : T.B.left ⟶ F.univ.A.left

  β₂ : (G2 T.B).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback T.B F.univ.A (u ≫ (LowChart.powA F T.r).hom) β
  sq : IsSquare β β₂
  lb : LBIso (abelian₂ T.B T.M.L) (F.univ.P.pull β₂)
  coord : ∀ i, (T.c₀ (Pi.single i 1)).left ≫ β = u ≫ (LowChart.coord F i).left

attribute [instance] LowBase.ring LowBase.loc

structure Taut {o : Type} [CommRing o] (ζ : o) (g n : ℕ) (φ : InvFun ℤ) extends LowBase ζ n where
  genus : h + T.r = g

  m : ℕ

  N : ℕ

  ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ))
  cone : IsCone id φ fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ))
  defin : ∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ)) x x

  R : Type
  [ringR : CommRing R]
  [domR : IsDomain R]
  [locR : IsLocalRing R]

  ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* R
  compl : IsComplAt ψ
  ψ_loc : IsLocalHom (ψ.comp MvPolynomial.C)
  bd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R
  tor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k)))

  Q : Data R

  e : Q.X ≃+ (Fin T.r → ℤ)
  data : DataFrom T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin T.r → ℤ))) n Q e

attribute [instance] Taut.ringR Taut.domR Taut.locR

namespace Taut

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ)

def iw : C.W →+* C.R := C.ψ.comp MvPolynomial.C

def b : o →+* C.R := C.iw.comp C.T.b

def s (k : Fin C.m ⊕ Fin C.N) : C.R := C.ψ (MvPolynomial.X k)

def t (k : Fin C.m) : C.R := C.s (.inl k)

def form (k : Fin C.m ⊕ Fin C.N) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ) := C.ε k

def δ (k : Fin C.m) : LinearMap.BilinForm ℤ C.Q.X := pull C.e.toIntLinearEquiv.toLinearMap (C.form (.inl k))

def IsFam (F : SFam g n ζ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X)
    (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) : Prop :=
  IsSemiAbelian G₁ ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ IsGenFibre F y α₁ ∧
    IsMumfordFam F y α₁ C.Q ∧ y ≫ F.s = jK C.R ≫ spMap C.b

end Taut

def IsMumPol {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁]
    (P : LB (G2 G₁).left) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧ IsSemiAbelian G₁ ∧ IsBiRig G₁ P ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left)
        (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'),
        IsGrpPullback G' G₁ (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)

def SameFib {S S' T : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S)
    (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (P' : LB (G2 A').left) (f' : T ⟶ S') : Prop :=
  ∃ (H : Over T) (_ : GrpObj H) (_ : IsCommMonObj H) (a : H.left ⟶ A.left) (a₂ : (G2 H).left ⟶ (G2 A).left)
    (a' : H.left ⟶ A'.left) (a₂' : (G2 H).left ⟶ (G2 A').left),
    IsGrpPullback H A f a ∧ IsSquare a a₂ ∧ IsGrpPullback H A' f' a' ∧ IsSquare a' a₂' ∧ LBIso (P.pull a₂) (P'.pull a₂')

def TorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K) (x : Over.mk (spMap κ ≫ jK R) ⟶ G), x ^ n = 1 →
    ∃ x₀ : Over.mk (jK R) ⟶ G, x.left = spMap κ ≫ x₀.left

def GalRigid {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ : R →+* R') (σ : R' ≃+* R'), IsCN R' → Function.Injective θ →
    θ.Finite → IsOfFinOrder σ → (∀ a, σ (θ (f a)) = θ (f a)) → (∀ r, σ (θ r) - θ r ∈ maximalIdeal R') → ∀ r, σ (θ r) = θ r

end GlobalTheory.TChart
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

structure VPre {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    (A : Type) [CommRing A] [IsLocalRing A] : Type 2 where
  posW : PosW W

  Y : Type 1

  V : Y → Type
  [ring : ∀ y, CommRing (V y)]
  [dom : ∀ y, IsDomain (V y)]
  [loc : ∀ y, IsLocalRing (V y)]
  cn : ∀ y, IsCN (V y)

  ev : ∀ y, A →+* V y
  ev_loc : ∀ y, IsLocalHom (ev y)

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  m : Y → ℕ

  t : ∀ y, Fin (m y) → V y
  t_mem : ∀ y i, t y i ∈ maximalIdeal (V y) ∧ t y i ≠ 0

  δ : ∀ y, Fin (m y) → LinearMap.BilinForm ℤ (X y)
  bal : ∀ y i, δ y i ∈ balForms bar (X y)
  nonneg : ∀ y i x, 0 ≤ δ y i x x
  pos : ∀ y x, x ≠ 0 → ∃ i, 0 < δ y i x x

  Q : Type

  u : ∀ y, (Fin s → X y) → Q → V y
  u_unit : ∀ y mu, ∃ c, IsUnit (u y mu c)

attribute [instance] VPre.ring VPre.dom VPre.loc VPre.add VPre.mod VPre.fin VPre.proj VPre.freeZ VPre.finZ

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]

def VSys.pre {N₁ : ℕ} (Φ : VSys bar q W N₁ A) : VPre bar q W A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit

namespace VPre
variable (Φ : VPre bar q W A)

def term (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) : Φ.V y := Φ.u y mu c * mono W (Φ.t y) (Φ.δ y) mu

def abelian₂ : Prop :=
  ∃ C : ℕ, ∀ y, Φ.m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Φ.ev y h ∣ Φ.t y i ^ (C * (Φ.δ y i x x).toNat)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → Φ.X y₀) (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A,
      ∀ (y : Φ.Y) (j : ℕ), ∃ S : Finset (Fin l × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ mu ∈ orbit O N₁ N (k y) a, mu ∉ S → (j : ℤ) ≤ ∑ i, lin W mu (Φ.δ y i)) ∧
        Φ.ev y f - ∑ mu ∈ S, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v)) ∈
          maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y)

def IsClassSum (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) {V' : Type} [CommRing V'] [IsLocalRing V']
    (io : Φ.V y →+* V') (x : V') : Prop :=
  ∀ j : ℕ, ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, ∀ v, CongMod N (mu v) (κ v)) ∧
    (∀ mu, (∀ v, CongMod N (mu v) (κ v)) → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
    x - io (∑ mu ∈ S, Φ.term y mu c) ∈ maximalIdeal V' ^ j

def Exact (N₁ : ℕ) : Prop :=
  ∀ (y : Φ.Y) (κ : Fin s → Φ.X y) (c : Φ.Q), ∃ h : A, Φ.IsClassSum y N₁ κ c (RingHom.id _) (Φ.ev y h)

def ClassSums [IsDomain A] (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ 1 ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (FractionRing A) L) (_ : Algebra A L)
      (_ : IsScalarTower A (FractionRing A) L) (_ : FiniteDimensional (FractionRing A) L) (_ : IsGalois (FractionRing A) L)
      (𝔷 : Ideal (integralClosure A L)) (f : (Fin s → Φ.X y₀) → Φ.Q → integralClosure A L), 𝔷.IsMaximal ∧
      (∀ κ κ' c, (∀ v, CongMod N (κ v) (κ' v)) → f κ c = f κ' c) ∧
      (∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsLocalRing V') (io : Φ.V y →+* V') (ev' : integralClosure A L →+* V'),
        io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧
        ev'.comp (algebraMap A _) = io.comp (Φ.ev y) ∧ (maximalIdeal V').comap ev' = 𝔷 ∧
        ∀ κ c, Φ.IsClassSum y N (fun v => k y (κ v)) c io (ev' (f κ c))) ∧
      ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
        ∃ ga : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (b : O) x, CongMod N (ga (b • x)) (b • ga x)) ∧ (N : ℤ) ∣ LinearMap.det ga - 1 ∧
          (∀ x, CongMod N₁ (ga x) x) ∧ ∀ κ c, σ (f κ c : L) = (f (fun v => ga (κ v)) c : L)

def rescale (v : ∀ y, (Φ.V y)ˣ) : VPre bar q W A :=
  { Φ with
    u := fun y mu c => Φ.u y mu c * v y
    u_unit := fun y mu => (Φ.u_unit y mu).imp fun _ h => h.mul (v y).isUnit }

def toVSys (N₁ : ℕ) (hl : Φ.abelian₂) (hf : Φ.Four N₁) : VSys bar q W N₁ A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit
  lam := hl
  four := hf

end VPre

end

namespace Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def IsThetaTerms₀ (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c)))

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z)

def RegAt (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) : Prop :=
  ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V₁)))

variable (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁))

def HasTraitsR : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev → RegAt X₁ z₁ ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMemberP [IsLocalRing V] (N₁ : ℕ) (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms₀ D N₁ e₈ fun mu c => Φ.term y (fun a => e.symm (mu a)) c

end Sep

end GlobalTheory.Poinc
end
end
