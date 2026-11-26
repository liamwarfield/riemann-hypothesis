module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesMetRankOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.TorusPart

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def genMap (U : Unif (maximalIdeal R) D A G) : A.A.left ⟶ G.left :=
  U.gen.inv.left ≫ pullback.fst G.hom (jK R)

def TorMatch (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
    (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' →
      a.left ≫ genMap U = a'.left ≫ genMap U' ≫ β

def Spread (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsDiscreteValuationRing V₁) (ψ : R →+* V₁)
    (G₁ : Over (Sp V₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left)
    (Ω : Type) (_ : Field Ω) (α : V₁ →+* Ω) (b : V →+* Ω) (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ G₁.left) (hn : IsGrpPullback GΩ G₁ (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n') (j : splitTorus (Sp V₁) D'.toPre.X ⟶ G₁)
    (G₀ : Over (Sp (ResidueField V₁))) (_ : GrpObj G₀) (m₀ : G₀.left ⟶ G₁.left)
    (hm₀ : IsGrpPullback G₀ G₁ (spMap (residue V₁)) m₀)
    (h₀ : ∀ x ∈ maximalIdeal R ^ (0 + 1), (residue V₁).comp ψ x = 0)
    (hm₀' : IsGrpPullback G₀ G (spMap ((residue V₁).comp ψ)) (m₀ ≫ φ₁)),
    IsLocalHom ψ ∧ IsGrpPullback G₁ G (spMap ψ) φ₁ ∧ IsMonHom j ∧ Function.Injective α ∧ α.comp ψ = b.comp g ∧
      n ≫ φ₁ = n' ≫ β ∧ pullTorus hn j = gtTorus (U'.gt 0) hb hn' ∧
      pullTorus hm₀ j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ gtTorus (U.gt 0) h₀ hm₀'

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)

def UOrdGe (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UOrdEq (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

section API

variable {M} {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ}

theorem uOrdEq_one (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : UOrdEq M T ξ 1 0 :=
  ⟨1, by rw [RatModel.val_one, pow_zero, Units.val_one, mul_one, map_one]⟩

end API

variable {M}

end Ord

def UTraitExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V →
    ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (T : UTrait Xo c) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧
        IsLocalHom f ∧ f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def UTraitUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) → Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X, ∀ a b, (m : ℤ) * T.be a b = m' * T'.be (e a) (e b)

def UPoinOnX (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Ext (D : DegPre R) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (GlobalTheory.TorusModel.splitExt D).IsGt H
  rep : GlobalTheory.TorusModel.Represents Φ

attribute [instance] Ext.grp Ext.comm


open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre in
instance (D : DegPre R) : Nonempty (Ext D) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (GlobalTheory.TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.TorusModel.exists_points hL hH
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ }⟩

def Ext.q {D : DegPre R} (Y : Ext D) : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

def IsTermOf {D : DegPre R} (Y : Ext D) {k : ℕ} {α : D.X} (b : D.SecB k α) (τ : SecK D.P.L Y.q.left k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J →
    sval τ x.left y J = sval b (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def VanMod (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) : Prop :=
  ∀ j : Fin 4 → D.P.L.ι, ((pullback.fst D.P.A.hom (thick R I e)).app _).hom (b.f j) = 0

structure IntFam (I : Ideal R) (D : DegPre R) (k : ℕ) where

  F : Fam D (FractionRing R) k

  f : ∀ α : D.X, D.SecB k α
  ext : ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α)
    (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left
    (scal (DegPre.BF D (FractionRing R)).hom 1)
  small : ∀ e : ℕ, {α | ¬ VanMod I (f α) e}.Finite

def IntFam.Lead {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k) (α : D.X) (b : D.SecB k α) : Prop :=
  F.f α = b ∧ ∀ β, β ≠ α → VanMod I (F.f β) 0

def PullB {R' : Type} [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) (b.f p) =
      (∏ κ, gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (D'.famφB x) q) (b'.f q)

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

structure Trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] where
  cdvr : GlobalTheory.LN.CDvr W

  φ : R →+* W
  inj : Function.Injective φ
  loc : IsLocalHom φ

  ξ : Sp W ⟶ C.S
  ξ_π : ξ ≫ C.π = spMap φ

  G : Over (Sp W)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]

  β : G.left ⟶ C.G.left
  cart : IsGrpPullback G C.G ξ β

  D' : DegData W (maximalIdeal W)

  A : PolAV (Sp (FractionRing W))

  U : Unif (maximalIdeal W) D' A G

  hD : IsPullDeg φ D.toPre D'.toPre

  ℓ : LB.Iso U.LG.L (C.P.L.L.pull β)
  ℓ_gen : ℓ.IsGen
  lab : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j))
      (p' : QkPt D'.toPre F (C.n ^ j)) (x' : TFK (R := W) F ⟶ A.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) ≫ β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α →
      QkToAkU U.toUnifPre F (C.n ^ j) p' x'

attribute [instance] Trait.grp Trait.comm

def Trait.Carries {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
    sval σ r z J = gs r z ⊤ (scal T.G.hom u) * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ k).val * sval σ' r z J'

def Trait.ExpBy {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ : SecK C.P.L.L T.β k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x),
    T.Carries u σ' σ ∧ (∀ x, PullB T.hD x (F.f (T.hD.xe x)) (f' x)) ∧ ∀ e, T.U.ExpandsAt e k σ' f'

def Trait.Exp {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) {k : ℕ}
    (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ σ : SecK C.P.L.L T.β k, T.ExpBy b σ F ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J

theorem LabCover.exists_trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    (φ : R →+* W) (ξ : Sp W ⟶ C.S) (hφ : Function.Injective φ) (hl : IsLocalHom φ) (hξ : ξ ≫ C.π = spMap φ) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (T : Trait C W'),
      Function.Injective io ∧ io.Finite ∧ T.φ = io.comp φ ∧ T.ξ = spMap io ≫ ξ := by
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hD, hW', hi, hf, hc, ⟨ℓ, hℓ⟩, hlab⟩ := C.trait W hW φ ξ hφ hl hξ
  have hio : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hf
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hi
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  refine ⟨W', inferInstance, inferInstance, inferInstance, io,
    { cdvr := hW', φ := io.comp φ, inj := hi.comp hφ, loc := inferInstance, ξ := spMap io ≫ ξ, ξ_π := ?_, G := G', β := β,
      cart := hc, D' := D', A := A', U := U', hD := hD, ℓ := ℓ, ℓ_gen := hℓ, lab := hlab }, hi, hf, rfl, rfl⟩
  rw [Category.assoc, hξ, ← Spec.map_comp]; rfl


end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def IsFlagBundle {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
    ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
      e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)



open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam.Pad

section One

variable {D : D7} (Y : ShimX D.what₂.Tau)


def bcFl : ℝ := (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j)) * testI Y

end One

def rkB (ι : Type) (N j : ℕ) (a : ι × Bool) : ℕ := cond a.2 j (N - j)

end GlobalTheory.CovTest

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

end GlobalTheory.CovHt

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolDeg GlobalTheory.TChart

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

structure PFactor (Q : Data R) (D' : DegPre R) where

  O : Type
  [ring : Ring O]
  [star : StarRing O]
  [mod : Module O D'.X]

  o : D'.OAct O

  e : O

  f : O

  inc : Q.B ⟶ (letI := D'.P.isAb.comm; D'.P.A)

  pr : D'.P.A ⟶ Q.B

  xi : Q.X →+ D'.X

  xp : D'.X →+ Q.X

  w : letI := D'.P.isAb.comm
    LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst Q.B Q.B ≫ inc) (snd Q.B Q.B ≫ inc ≫ o.onB.act f) : G2 Q.B ⟶ G2 D'.P.A).left)
  idem : e * e = e
  inc_hom : IsMonHom inc
  pr_hom : IsMonHom pr
  inc_pr : inc ≫ pr = 𝟙 _
  pr_inc : pr ≫ inc = o.onB.act e
  xp_xi : ∀ y, xp (xi y) = y
  xi_xp : ∀ z, xi (xp z) = e • z
  c_xi : ∀ y, D'.c (xi y) = Q.c y ≫ inc
  inj : Function.Injective fun y => Star.star e • f • xi y
  onto : ∀ z, ∃ y, Star.star e • z = Star.star e • f • xi y
  w_gen : w.IsGen
  tau : ∀ a b z J J', Good D'.P.L z J → Good Q.M.L z J' →
    val (Q.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
        val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J
  alg : (∃ b : ℕ, 0 < b ∧ Star.star e * e = b • (Star.star e * f * e)) ∧
    Star.star e * f * e = Star.star e * Star.star f * e ∧ ∃ g : O, g * (Star.star e * f * e) = e

attribute [instance] PFactor.ring PFactor.star PFactor.mod

def Canon [IsLocalRing R] (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) : Prop :=
  P.IsLB ∧ ∃ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R))
    (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O)
    (inc : G ⟶ G') (pr : G' ⟶ G), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsMonHom inc ∧ IsMonHom pr ∧
      inc ≫ pr = 𝟙 G ∧ pr ≫ inc = oG.act F.e ∧
      LBIso P ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev RootFn (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type 1 :=
  ∀ (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D' → D'

variable {A : Over (Sp R)} [GrpObj A]


def HasRoots (A : Over (Sp R)) [GrpObj A] (n : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
    (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x

def IsTorsChar (n : ℕ) (b : Fn0 A) : Prop :=
  (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (w : Pt A D),
    w ^ n = 1 → b D' (spOver φ ≫ w) = φ (b D w)) ∧
  ∀ (D : Type) [CommRing D] [Algebra R D] (w w' : Pt A D), w ^ n = 1 → w' ^ n = 1 → b D (w * w') = b D w + b D w'

def IsSec (n : ℕ) (b : Fn0 A) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) (s : RootFn A D) : Prop :=
  (∀ (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D')
    (ψ : D' →ₐ[R] D'') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z)) ∧
  ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'),
    z ^ n = spOver φ ≫ x → w ^ n = 1 → s D' φ (z * w) = s D' φ z + b D' w

abbrev SecFam (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → RootFn X D

def IsSecDiff (n : ℕ) (S : SecFam A) (u : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E) (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
    ψ (u D D' φ x) = S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z

def IsSecAdd (n : ℕ) (S : SecFam A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (z w : Pt A E), z ^ n = spOver ψ ≫ x → w ^ n = spOver ψ ≫ y →
    ψ (g D x y) = S D (x * y) E ψ (z * w) - S D x E ψ z - S D y E ψ w


variable (R) in
def diagSum (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) : D ⊗[R] D →ₗ[R] D :=
  ∑ i ∈ Finset.range m, (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D)
    fun _ _ ↦ Commute.all _ _).toLinearMap

theorem diagSum_tmul (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) (a b : D) :
    diagSum R D m (a ⊗ₜ b) = ∑ i ∈ Finset.range m, mulBy R D i a * b := by
  simp [diagSum, LinearMap.sum_apply]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def Fn1.pull {X Y : Over (Sp R)} (q : Y ⟶ X) (u : Fn1 X) : Fn1 Y := fun D _ _ D' _ _ φ y ↦ u D D' φ (y ≫ q)

section Alg

variable {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']

def ptAlg (z : Pt (SpAlg R D) E) : D →ₐ[R] E :=
  { (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom with
    commutes' := fun r ↦ by
      have h : CommRingCat.ofHom (algebraMap R D) ≫
          Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left =
          CommRingCat.ofHom (algebraMap R E) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact Over.w z
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h }

theorem spOver_ptAlg (z : Pt (SpAlg R D) E) : spOver (ptAlg z) = z := by
  apply Over.OverMorphism.ext
  rw [spOver_left]
  exact Spec.map_preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left

theorem ptAlg_spOver (α : D →ₐ[R] E) : ptAlg (spOver α) = α := by
  refine AlgHom.ext fun r ↦ ?_
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) (spOver α).left).hom r = α r
  rw [spOver_left]
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) (Spec.preimage_map (CommRingCat.ofHom (α : D →+* E)))

theorem ptAlg_comp (ψ : E →ₐ[R] E') (z : Pt (SpAlg R D) E) : ptAlg (spOver ψ ≫ z) = ψ.comp (ptAlg z) := by
  conv_lhs => rw [← spOver_ptAlg z, spOver_comp]
  exact ptAlg_spOver _

def epsEv (e : Pt (epsR R) E) : DualNumber E →ₐ[R] E :=
  DualNumber.lift ⟨(AlgHom.id R E, ptAlg (D := DualNumber R) e DualNumber.eps), by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩

end Alg

section Param

variable {A B : Over (Sp R)} {J : Type} [Fintype J] {D : Type} [CommRing D] [Algebra R D]

def sumMul (d : J → D) (b : J → Fn1 B) : Fn1 (SpAlg R D ⊗ B) := fun E _ _ E' _ _ ψ z ↦
  ∑ i, ψ (ptAlg (z ≫ fst _ _) (d i)) * b i E E' ψ (z ≫ snd _ _)

def IsCupCob {K : Type} (W : K → (A ⊗ B).left.Opens) (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) : Prop :=
  ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
    [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), Sm W z →
    ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) =
      ∑ i, ψ (a i E E' φ (z ≫ fst _ _)) * b i E' E'' ψ (spOver φ ≫ z ≫ snd _ _)

def parCoc (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (x : Pt A D) : Fn1 (SpAlg R D ⊗ B) :=
  fun E _ _ E' _ _ ψ z ↦ n E E' ψ (z ≫ x ▷ B) -
    ∑ i, ψ (a i D E (ptAlg (z ≫ fst _ _)) x) * b i E E' ψ (z ≫ snd _ _)

def parCov {K : Type} (W : K → (A ⊗ B).left.Opens) (x : Pt A D) : K → (SpAlg R D ⊗ B).left.Opens :=
  fun i ↦ (x ▷ B).left ⁻¹ᵁ W i

end Param

section Change

variable {R' : Type} [CommRing R'] (σ : R →+* R')

@[reducible] def algVia (E : Type) [CommRing E] [Algebra R' E] : Algebra R E :=
  ((algebraMap R' E).comp σ).toAlgebra

def homVia {E E' : Type} [CommRing E] [Algebra R' E] [CommRing E'] [Algebra R' E'] (ψ : E →ₐ[R'] E') :
    @AlgHom R E E' _ _ _ (algVia σ E) (algVia σ E') :=
  @AlgHom.mk R E E' _ _ _ (algVia σ E) (algVia σ E') (ψ : E →+* E') fun r ↦ ψ.commutes (σ r)

variable {σ} {X : Over (Sp R)} {X' : Over (Sp R')} {q : X'.left ⟶ X.left}

def ptVia (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E : Type} [CommRing E] [Algebra R' E] (y : Pt X' E) :
    @Pt R _ X E _ (algVia σ E) :=
  Over.homMk (y.left ≫ q) (by
    have h : y.left ≫ X'.hom = spMap (algebraMap R' E) := Over.w y
    change (y.left ≫ q) ≫ X.hom = spMap ((algebraMap R' E).comp σ)
    rw [Category.assoc, w, ← Category.assoc, h, Cris.spMap_comp])

def bcPull (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) : Fn1 X' := fun E _ _ E' _ _ ψ y ↦
  @u E _ (algVia σ E) E' _ (algVia σ E') (homVia σ ψ) (ptVia w y)

end Change

section Gen

variable {X Y : Over (Sp R)}

def IsPtGen (L : LB X.left) (q : Y ⟶ X)
    (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → IsUnit (t E z i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E)
    (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → t E' (spOver ψ ≫ z) i = ψ (t E z i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i j : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i →
    ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U j → t E z i = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val * t E z j

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def IsEpsGen (P : LB (A ⊗ B).left) (v : epsR R ⟶ B)
    (T : ∀ (E : Type) [CommRing E] [Algebra R E], Pt A E → P.ι → DualNumber E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → IsUnit (T E x i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (x : Pt A E)
    (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → T E' (spOver ψ ≫ x) i = epsHom ψ (T E x i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i j : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
    ⊤ ≤ x.left ⁻¹ᵁ chartsA P j → T E x i = evU (ptV v x).left (P.U i ⊓ P.U j) (P.g i j).val * T E x j

end Gen

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.EndModel
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem endData_of_oAct {R : Type} [CommRing R] [IsDomain R] (O : Type) [Ring O] [StarRing O] (D : DegPre R)
    [Module O D.X] (io : D.OAct O) (a : O) :
    EndData D (io.onB.act a) (io.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨io.onB.hom a, io.onB.hom (star a), io.onB.rosati a, io.c_lin a, io.c_lin (star a), io.tau_bal a⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem thickMap_map {G H : Over (Sp R)} (b : G ⟶ H) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e H := by
  apply pullback.hom_ext
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
    rfl
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    simp

end GlobalTheory.Mum.EndModel
end
end
