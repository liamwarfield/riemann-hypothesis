module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

abbrev Fld (Z : Scheme.{0}) : Type := ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}

def IsTr {S : Type} [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (v : TanM (𝟙 (Sp R)) G)
    (w : Sp (DualNumber S) ⟶ G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ G.hom) ⟶ G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ (tv v).left ∧ (g' * v').left = w

def IsInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) : Prop :=
  IsField ⊤ dd ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (w : Sp (DualNumber S) ⟶ G.left)
    (O : G.left.Opens) (f : Γ(G.left, O)), g ≫ G.hom = spMap φ → ⊤ ≤ g ⁻¹ᵁ O → IsTr G φ g v w →
      (valR w O f).snd = valR g O (dd O f)

def IsLift (D : R → R) (W : G.left.Opens) (d : Fld G.left) : Prop :=
  IsField W d ∧ ∀ O, O ≤ W → ∀ r, d O (constFn G.hom O r) = constFn G.hom O (D r)

variable {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R)

def dlg (δ : Fld G.left) (i i' : L.ι) (O : G.left.Opens) : Γ(G.left, O) :=
  δ O (pbT m (L.g i i').val O) * pbT m (L.g i i')⁻¹.val O

def KSRel (Θ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (J : Type) (W : J → G.left.Opens) (j : J → L.ι) (d : J → Fld G.left),
    ⨆ i, W i = ⊤ ∧ (∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)) ∧ (∀ i, IsLift G D (W i) (d i)) ∧
    ∀ i i' O, O ≤ W i ⊓ W i' → ∀ f, d i O f - d i' O f =
      ∑ a, ∑ b, constFn G.hom O (Θ a b) * dlg G m L (dd b) (j i) (j i') O * dd a O f

def op (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    (O : G.left.Opens) (f : Γ(G.left, O)) : Γ(G.left, O) :=
  2 * (k : Γ(G.left, O)) * d O f - ∑ a, ∑ b, constFn G.hom O (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, constFn G.hom O (u a) * dd a O f + (2 * (k : Γ(G.left, O)) ^ 2 * rsT p O + 2 * (k : Γ(G.left, O)) * rsT p' O) * f

structure Heat where

  Θ : Matrix (Fin n) (Fin n) R
  symm : Θᵀ = Θ

  u : Fin n → R

  J : Type

  W : J → G.left.Opens

  j : J → L.ι

  d : J → Fld G.left

  p : ∀ i, Γ(G.left, W i)

  p' : ∀ i, Γ(G.left, W i)
  cover : ⨆ i, W i = ⊤
  le : ∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)
  lift : ∀ i, IsLift G D (W i) (d i)
  glue : ∀ (k : ℕ) i i' O, O ≤ W i ⊓ W i' → ∀ f,
    op G dd Θ u (d i) (p i) (p' i) k O (pbT m (L.g (j i) (j i')).val O ^ k * f) =
      pbT m (L.g (j i) (j i')).val O ^ k * op G dd Θ u (d i') (p i') (p' i') k O f

abbrev SecM {Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ))

variable {G m L dd D}

def Heat.Acts (h : Heat G m L dd D) (k : ℕ) (τ τ' : SecM m L k) : Prop :=
  ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) =
    op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i))

end General

def ringOp {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω)
    (p p' : Ω) (k : ℕ) (f : Ω) : Ω :=
  2 * (k : Ω) * d f - ∑ a, ∑ b, Θ a b * dd a (dd b f) + 2 * ∑ a, u a * dd a f + (2 * (k : Ω) ^ 2 * p + 2 * (k : Ω) * p') * f

def epsHom {Ω : Type} [CommRing Ω] (δ : Derivation ℤ Ω Ω) : Ω →+* DualNumber Ω where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_zero' := by simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]

def IsValue {X Y : Scheme.{0}} {Ω : Type} [CommRing Ω] (m : Y ⟶ X) (L : LB X) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ m)) (k : ℕ) (σ : SecM m L k) (s : Ω) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z) (J), Good L z J →
    sval σ (r ≫ x) z J = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom s) * (val g r z J ^ k).val

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

def IsTerm (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good Q.P.L y J →
    sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def IsWt (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (a a' : Sp S ⟶ Y.H.left), a = x.left → a' = x'.left → ⊤ ≤ a ⁻¹ᵁ V → ⊤ ≤ a' ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
    (∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
    valR a' V f = c α * valR a V f

variable {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

def IsBasic : Prop :=
  ∀ i, (∃ V : Q.P.A.left.Opens, h.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h.p i) ∧ IsWt Y 0 _ (h.p' i) ∧
    ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
      IsWt Y α (Y.q.left ⁻¹ᵁ V) (h.d i _ f)

def TActs (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) : Prop :=
  ∃ τ τ', IsTerm Y k α σ τ ∧ IsTerm Y k α σ' τ' ∧ h.Acts k τ τ'


variable (Q) in
def ShiftEq (k : ℕ) (mu α : Q.X) (σ : Q.SecB k α) (σ₁ : Q.SecB k (α + k • mu)) (c : R) (σ₂ : Q.SecB k (α + k • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k)), u.IsGen →
    LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α) →
    ∀ z J, Good Q.P.L z J →
      sval σ₁ (DegPre.prB Q (FractionRing R)).left z J =
        (val u (𝟙 _) z J).val * sval σ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
          gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J

def HasDefect (c : ℕ → Q.X → Q.X → R) : Prop :=
  ∀ (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)), 1 ≤ k →
    ShiftEq Q k mu α σ σ₁ 0 σ₁ → TActs Y h k α σ σ' → TActs Y h k (α + k • mu) σ₁ σ₁' →
      ShiftEq Q k mu α σ' σ₁' (c k mu α) σ₁

end Raynaud

end GlobalTheory.Heat
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyEven

def KeyOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G) (ψ : LB.Iso x.P.L (L.L.pull φ))
    (F : DualNumber R →+* DualNumber K),
    IsGrpPullback x.P.A G (spMap f) φ ∧ ψ.IsGen ∧
    LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L.L L.rig) ∧
    (∀ (j : (L.L.pull φ).ι) (i : x.P.L.ι) (h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.L.pull φ).U j ⊓ x.P.L.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (y i).left

def HasUnif {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (L : LB G.left) : Prop :=
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V)))
    (U : Unif (IsLocalRing.maximalIdeal V) D A G), LBIso U.LG.L L

def UnifAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ ξ : Sp V ⟶ S, (ξ ⁻¹' abLocus G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)],
      HasUnif ((Over.pullback ξ).obj G) (L.pull (pullback.fst G.hom ξ))

def PolOnAb {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ W : S.Opens, (W : Set S) ⊆ abLocus G →
    RelAmple ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι)) ∧
    KTriv ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι))

def NzFib {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec) : Prop :=
  ∀ s : S, ∃ z : G.left, G.hom z = s ∧ z ∈ nonzeroLocus σ

def KeyTrait (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
      (y : Fin x.P.g → (epsR V ⟶ G)), IsSemiAbelian G → HasUnif G L.L → IsLieBasis y → NzFib σ →
      KeyOn (algebraMap V (FractionRing V)) x G L σ y →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyTraitU (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ σ : U.LG.L.Sec, NzFib σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyLoc (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A]
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing A))
    (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → SmoothOfRelativeDimension x.P.g G.hom → IsOpen (abLocus G) →
    L.IsSymmetric → PolOnAb G L.L → UnifAlong G L.L → IsLieBasis y → NzFib σ →
    KeyOn (algebraMap A (FractionRing A)) x G L σ y →
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u

def KeyGlob : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → IsIntegral S → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge G g) 4)

end GlobalTheory.KeyEven

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

structure Trait (F : SFam g n ζ) where

  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V

  ϖ : V
  irr : Irreducible ϖ

  y : Sp (FractionRing V) ⟶ F.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  D : DegData V (maximalIdeal V)

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  α : A.A.left ⟶ F.univ.A.left

  α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback A.A F.univ.A y α
  sq : IsSquare α α₂
  lb : LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

  β : LinearMap.BilinForm ℤ D.toPre.X
  symm : ∀ a b, β a b = β b a
  mono : IsMonomial D.toPre ![ϖ] ![β]

attribute [instance] Trait.ring Trait.dom Trait.dvr Trait.char Trait.grp Trait.comm

def ValOn (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j →
    ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a}

def SharpOver (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) : Prop :=
  ∃ c : SiegPre g n ζ (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

def ThetaInt (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) : Prop :=
  ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) →
    ∀ (M : RatModel o' Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z → M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i →
      M.HasDiv S.th

def IsNormBl {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData) : Prop :=
  IsNormalScheme S ∧ ∃ (S₀ : Scheme.{0}) (π₀ : S₀ ⟶ Z) (ν : S ⟶ S₀) (U : S₀.Opens), FinalTheorems.Blowup π₀ J ∧ ν ≫ π₀ = π ∧
    IsFinite ν ∧ Dense (U : Set S₀) ∧ Dense (ν ⁻¹' U : Set S) ∧ IsIso (ν ∣_ U)

def IsThetaCompact (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) : Prop :=
  IsProjOver z ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧
    ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ThetaInt F W i

def IdealSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d

def PoinSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ OZ : LB Z, OZ.IsLB → IsAmpleLB OZ → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S),
        1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧ IsProjOver (π ≫ z) ∧
        IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
        BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d ∧
        ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam

def shimXOfPkg {D : D7} {G : DV.Geo D.what₂.LL} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {N j : ℕ} {Comp : Type} [Fintype Comp] [Nonempty Comp] (cx : CxPkg D.what₂.Tau N j Comp)
    (alg : AlgPkg G D.what₂.Tau N Comp) (pad : PadPkg D N j Comp jC ng) (h : 1 ≤ j ∧ j < N) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := Comp
  vol := cx.vol
  chern := cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N cx.vol P d hd hP
  arDeg := pad.arDeg
  arDeg_homog := pad.arDeg_homog
  arMix := pad.arMix
  arMix_HT := pad.arMix_HT
  arMix_DR := pad.arMix_DR
  CurveHT := pad.CurveHT
  degHT := pad.degHT
  CurveDR := pad.CurveDR
  degDR := pad.degDR
  FibComp := pad.FibComp
  fibInBd := pad.fibInBd
  Pt := pad.Pt
  phiDR := pad.phiDR
  phiMod := pad.phiMod
  phiFr := pad.phiFr
  XC := cx.XC
  rfn := cx.rfn
  rfn_ge := cx.rfn_ge
  hLo := cx.hLo
  hUp := cx.hUp
  hLo_le := cx.hLo_le
  connN := cx.connN
  curvN := cx.curvN
  compOf := cx.compOf
  normDetInf := cx.normDetInf
  compPt := pad.compPt
  normDetT := pad.normDetT
  normDetH := pad.normDetH
  htDetT := pad.htDetT
  ALB := alg.ALB
  arSelf := fun L => ∑ c, alg.arSelfC L c
  arSelfC := alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, alg.geoC L c
  geoC := alg.geoC
  geo_sum := fun _ => rfl
  arVol := alg.arVol
  semipos := alg.semipos
  nefFib := alg.nefFib
  arNef := alg.arNef
  Mbar := alg.Mbar

section
variable {D : D7} {A : Amb D} {F : SrcFam A} {L : CmList A} {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C)
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (k : Kits F L C jC ng)

end

end GlobalTheory.ShFam
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Comb

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def lnAdl (A : Adl C Y) (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  lnN (A.m σ) (genAt A.D (under z)) z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ)

end Comb

section Base

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

def LiesUnder (k : s.Comp) (y : Pt s) (x : (Φ.C k).Y.X) : Prop :=
  ∃ p : Sp Qb ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = y.y ∧ (Φ.C k).Carries p y.frame ∧ below p = x

def baseOn (k : s.Comp) (y : Pt s) : (Φ.C k).Y.X := Classical.epsilon (LiesUnder Φ k y)

abbrev basePt (y : Pt s) : (Φ.C (compPt s y)).Y.X := baseOn Φ (compPt s y) y

variable {Φ}

theorem LiesUnder.compPt_eq {k : s.Comp} {y : Pt s} {x : (Φ.C k).Y.X} (h : LiesUnder Φ k y x) : compPt s y = k := by
  obtain ⟨p, hp, -, -⟩ := h
  let o : Sp Qb := IsLocalRing.closedPoint Qb
  refine (PtComp.existsUnique_onComp s (y.y o)).unique (PtComp.onComp_compPt s y o) ?_
  obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  refine ⟨⟨z, hz⟩, fun pt => ?_⟩
  exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨p o, by rw [← hp]; rfl⟩
    (Φ.label k ⟨z, hz⟩ pt)


variable (Φ) in
theorem existsUnique_liesUnder (y : Pt s) : ∃! x, LiesUnder Φ (compPt s y) y x := by
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨⟨k, p⟩, hp, hu⟩ := Φ.lifts Qb y.fK y.y y.y_over y.frame
  obtain rfl : compPt s y = k := LiesUnder.compPt_eq ⟨p, hp.1, hp.2, rfl⟩
  refine ⟨below p, ⟨p, hp.1, hp.2, rfl⟩, ?_⟩
  rintro _ ⟨q, h₁, h₂, rfl⟩
  rw [eq_of_heq (Sigma.mk.inj (hu ⟨_, q⟩ ⟨h₁, h₂⟩)).2]


variable (Φ) in
theorem liesUnder_basePt (y : Pt s) : LiesUnder Φ (compPt s y) y (basePt Φ y) :=
  Classical.epsilon_spec (existsUnique_liesUnder Φ y).exists

end Base

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def rootEx (τ : E →+* ℂ) (i : ℕ) : Letter Dw → ℤ := expo Dw (rootSym Dw (fun _ => false) none τ i)


open Classical in
theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 :=
  Finsupp.sum_single_index (by simp)

end Roots

structure MetIn {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) : Type where

  hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)

  h0 : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

  r : ∀ k σ, Pts (Φ.C k).Y σ → ℝ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  dir : D.what₂.Tau → Fin N → ℝ

  reg : ∀ k σ, (D.what₂.Tau → Fin N → ℝ) → ℝ → Pts (Φ.C k).Y σ → ℝ

structure Setup (D : D7) : Type 1 where

  A : Amb D

  N : ℕ

  j : ℕ
  indef : 1 ≤ j ∧ j < N

  S : Sig A N j

  κ : Lv A

  s : FinalTheorems S κ

  L : CmList A

  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N

  B : s.Bd L

  fl : s.Comp → D.what₂.Tau → ℂˣ

  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

  ng : NgPkg

  loc : LocSt D N j ng

  glob : GlobSt fun p => (loc.loc p).Mdl

  adm : AdmSt D N j jC

  met : MetIn Φ

namespace Setup

variable {D : D7} (O : Setup D)

def pad : PadPkg D O.N O.j O.s.Comp O.jC O.ng :=
  padAt O.s O.loc O.glob O.adm (flatSt O.s O.Φ O.met.hm) (arIn O.s O.Φ O.met.hm)

def kit (key : KeySec O.s.Xo O.κ.c) : Kit O.s O.L (cxSt D.what₂.LL) O.jC O.ng :=
  ⟨O.Φ, O.dim_eq, key, O.B, O.fl, O.Mb, O.pad, fun _ => Iff.rfl⟩

def Y : DV.ShimX D.what₂.Tau :=
  shimXOfPkg (O.s.cx O.L O.B O.fl) (O.s.alg O.L (cxSt D.what₂.LL) (cutSt _) (resSt _) O.Φ O.dim_eq O.Mb) O.pad O.indef
    O.κ.primes fun _ hp => Nat.prime_of_mem_primeFactors hp

abbrev var (c : O.s.Comp) : Var D.what₂.LL := (O.Φ.C c).Y

abbrev ex (x : DV.Rt D.what₂.Tau O.N) : Letter O.S.Dw → ℤ := rootEx O.S.Dw (DV.tauEmb D x.1) x.2

def adl0 (c : O.s.Comp) (w : Sym D.host.E →₀ ℤ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (fun _ => O.met.h0 c) w

def htWt {c : O.s.Comp} (ρ : DV.Rt D.what₂.Tau O.N → Adl (cxSt D.what₂.LL) (O.var c)) (u : D.what₂.Tau → Fin O.N → ℝ)
    (z : (O.var c).X) : ℝ := -∑ x, u x.1 x.2 * (ρ x).ht z

def chg (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : ℝ :=
  ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * lnRatio (O.met.hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) z

structure LatModel (P : Finset ℕ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  line : Finset ℕ → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ → HermLB V.p
  line_spec : ∀ Q ⊆ P, ∀ st, (letterOf O.S.Dw st).isSome →
    V.Induces (O.adl0 c (Finsupp.single (ArIn.ind Q, none, st) 1)) (line Q st) 1

  k : ℕ
  k_pos : 0 < k

  amp : HermLB V.p
  amp_spec : V.Induces (O.met.ab c) amp k

namespace LatModel

variable {O} {P : Finset ℕ} {c : O.s.Comp} (W : O.LatModel P c)

end LatModel

end Setup

end GlobalTheory.Mean4O
end
end
