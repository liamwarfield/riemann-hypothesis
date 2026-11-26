module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

namespace Sep
open GlobalTheory.ZH

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

structure Tower (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X₂ : Setup F W i

  act₂ : Matrix (Fin 8) (Fin 8) ℤ → (X₂.ρ.P.A ⟶ X₂.ρ.P.A)
  isAct : IsAct X₂ act₂
  [alg : Algebra X₁.Ω₁ X₂.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X₂.Ω₁
  gal : IsGalois X₁.Ω₁ X₂.Ω₁
  deg : ∃ e, Module.finrank X₁.Ω₁ X₂.Ω₁ = X₁.ρ.n ^ e

  d : ℕ
  lev : X₂.S.r * X₂.S.N = X₁.S.r * X₁.S.N * d

  om : X₁.S.R →+* X₂.S.R
  om_eq : ∀ a, (om a : X₂.Ω₁) = algebraMap X₁.Ω₁ X₂.Ω₁ a
  om_fin : om.Finite

  sR : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.R →+* X₂.S.R)
  sR_eq : ∀ σ a, (sR σ a : X₂.Ω₁) = σ a

  p : X₂.M.Z ⟶ X₁.M.Z
  p_fin : IsFinite p
  p_pt : X₂.M.pt ≫ p = spMap (algebraMap X₁.Ω₁ X₂.Ω₁) ≫ X₁.M.pt
  p_π : p ≫ X₁.π = X₂.π

  φ : X₂.ρ.P.A.left ⟶ X₁.ρ.P.A.left
  cart : IsGrpPullback X₂.ρ.P.A X₁.ρ.P.A (spMap om) φ
  lb : LBIso X₂.ρ.P.L (X₁.ρ.P.L.pull φ)
  act_eq : ∀ a, (act₂ a).left ≫ φ = φ ≫ (act a).left

  lam : X₁.S.Gam →+ X₂.S.Gam
  lam_pt : ∀ a, (X₂.ρ.pt (lam a)).left ≫ φ = spMap om ≫ (X₁.ρ.pt a).left
  lam_range : ∀ a', ∃ a, lam a = d • a'

  gl : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.Gam →+ X₂.S.Gam)
  gl_pt : ∀ σ a, (X₂.ρ.pt (gl σ a)).left ≫ φ = spMap (sR σ) ≫ (X₂.ρ.pt a).left ≫ φ
  gl_lam : ∀ σ a, gl σ (lam a) = lam a

attribute [instance] Tower.alg

def Tower.Ext {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z}
    {z₂ : 𝔗.X₂.M.Z} {V V' : Type} [CommRing V] [CommRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') : Prop :=
  IsLocalHom ev₂ ∧ ∀ x x₂, 𝔗.X₂.M.stalkHom z₂ x₂ = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) → ev₂ x₂ = io (ev x)

end Sep

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

def hs (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * ((m - j).choose j : ℝ)) * X 0 ^ (m - 2 * j) * X 1 ^ j

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fld (w : A.Pt → Ev n) : A.Fld := fun x => w x

def evalF {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) : A.Fld :=
  fld A fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))

def wInt [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) : ℝ := ∫ y, g y ∂A.part α 1 - ∫ y, g y ∂A.part α (-1)

theorem wInt_one [MeasurableSpace M] (α : A.Fld) : wInt A (fun _ => 1) α = A.integral α := by
  simp [wInt, HolAtlas.integral]

end Manifold

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {D D' : ℕ}

variable (h : IsRegVar p D) (h' : IsRegVar p' D') (σ : k →+* ℂ)

end GlobalTheory.LineForm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (ω : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (D : DegPre V)
  (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left)
  (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))

def From : Prop :=
  IsGrpPullback D.P.A T.B (spMap ω) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ω ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap ω) z J)

def TautPt (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ) (g : GtPtF D F) : Prop :=
  g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left ∧
    ∀ χ, ∃ k : Fˣ, (k : F) = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i (e χ) a ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (g.s χ) (𝟙 _) z J' = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) *
          (lamVal w (lift (DegPre.cF D F χ) g.b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J)

end From

section Tr

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Ext (f : R →+* V) {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) : Prop :=
  ∀ r, j (algebraMap (FractionRing R) F₀ (algebraMap R (FractionRing R) r)) =
    algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (f r))

def Tr (f : R →+* V) {D₀ : DegPre R} {D : DegPre V} (hD : IsPullDeg f D₀ D) {F₀ F : Type} [Field F₀]
    [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀) (g : GtPtF D F) :
    Prop :=
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  ∃ g₁ : GtPtF D₀ F, (g₁.b.left = spMap j ≫ g₀.b.left ∧
    ∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) ∧ IsPullGtF f hD F g₁ g

end Tr

def OverPt {X : Scheme.{0}} {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre h n ζ sX) {S : Scheme.{0}}
    (A : PolAV S) (y : S ⟶ X) (α : A.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback A.A c.A y α ∧ ∃ α₂ : (G2 A.A).left ⟶ (G2 c.A).left, IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (c.P.pull α₂)

def Match {V : Type} [CommRing V] [IsDomain V] (D₁ D₂ : DegPre V) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F]
    [Algebra (FractionRing V) F] : Prop :=
  IsMonHom b ∧ IsIso b ∧
    LBIso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₂.P.A D₂.P.L).pull
      (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left) ∧
    (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (φ.symm.toAddMonoidHom χ) χ), Nrm u) ∧
    ∀ (y : D₁.X) (g : GtPtF D₁ F), GtPtF.IsIota y g →
      ∃ g' : GtPtF D₂ F, Act D₁ D₂ b φ.symm.toAddMonoidHom g g' ∧ GtPtF.IsIota (φ y) g'

def QImg {V : Type} [CommRing V] [IsDomain V] {D₁ D₂ : DegPre V} (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) {F : Type} [Field F]
    [Algebra (FractionRing V) F] {k : ℕ} (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k) : Prop :=
  ∃ p' : QkPt D₂ F k, p'.y = φ p₁.y ∧ Act D₁ D₂ b φ.symm.toAddMonoidHom p₁.g p'.g ∧ QkPt.Equiv D₂ F p' p₂

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

variable {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def ThAt (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {N : ℕ} (f : F.X ⟶ PSpace (cycAway n) N) : Prop :=
  P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ Odd m ∧ 3 ≤ m ∧ IsUnit (m : cycAway n) ∧
    N + 1 = m ^ (4 * (8 * g)) ∧ f ≫ PSpace.str (cycAway n) N = F.s ∧ ThMap P.A P.L rig m (𝟙 F.X) f ∧ IsE8 W

def QFin {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}

def SymE {S : ThetaSys o Ω} (ρ : S.Real) (m : ℕ) {N : ℕ} (e : Fin N → Ω) : Prop :=
  N = m ^ (4 * S.g) ∧ (m : Ω) ≠ 0 ∧ SymAt ρ.P.A ρ.P.L ρ.rig m (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ S.R.val.toRingHom) e

def SysAt (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) : Prop :=
  β.Finite ∧ Function.Injective β ∧ S.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W ρ.P u ∧
    u ≫ F.s = spMap (algebraMap o S.R) ≫ spMap β

def LevAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X) : Prop :=
  Geo.Tor.IsNormalScheme Y.Z ∧ IsFinite q ∧ Surjective q ∧ q ≫ F.s = Y.s ≫ spMap β ∧
    Y.pt ≫ q = spMap S.R.val.toRingHom ≫ u

def OpenAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (M : RatModel o Ω) (U : M.Z.Opens)
    (c : U.toScheme ⟶ F.X) : Prop :=
  (U : Set M.Z).Nonempty ∧ IsFinite c ∧ Surjective c ∧ c ≫ F.s = U.ι ≫ M.s ≫ spMap β ∧
    ∀ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt → x ≫ c = spMap S.R.val.toRingHom ≫ u

def MinorAt (S : ThetaSys o Ω) (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) : Prop :=
  X.IsNm S.th ∧ IsProjOver X.s ∧ Geo.Tor.IsNormalScheme X.Z ∧ S.Over₀ M U₀ ∧ S.IsEE M U₀ EE ∧ X.IsHom M (AlgHom.id o Ω) f ∧
    (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab)

def SameScale (M : RatModel o Ω) {I J : Type} (a : I → Ω) (b : J → Ω) (D : ℕ) : Prop :=
  ∀ z i, M.Div a i z → ∃ j, M.Div b j z ∧ a i ^ D / b j ∈ M.O z ∧ b j / a i ^ D ∈ M.O z

end GlobalTheory.SiegTh

end
end
