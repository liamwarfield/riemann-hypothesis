module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc

section Fields

variable {X Y V : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def gp (X : Scheme.{0}) [IsIntegral X] : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

def cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : R →+* X.functionField :=
  (fnOf ⊤ trivial).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def PFF (i : V ⟶ Y) (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) : Prop :=
  ∃ l : Sp Y.functionField ⟶ V, l ≫ i = gp Y ∧ l ≫ φ = spMap θ ≫ gp X

def PPull (i : V ⟶ Y) (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D' : CartierDiv Y) : Prop :=
  ∀ (v : V) (g : X.functionFieldˣ), D.IsEqn (φ v) g → D'.IsEqn (i v) (Units.map θ.toMonoidHom g)

def Sec (D : CartierDiv X) (k : ℕ) : Set X.functionField := {u | ∀ x, (k • D).RegularAt x u}

def locus (D : CartierDiv X) (k : ℕ) (u : X.functionField) : Set X := {x | (k • D).GeneratesAt x u}

def AmpleDiv (D : CartierDiv X) : Prop :=
  ∀ x : X, ∃ k, 1 ≤ k ∧ ∃ u ∈ Sec D k, ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X) = locus D k u ∧ x ∈ U

def regSet (x : X) : Set X.functionField := {u | RegAt x u}

end Fields

def Vert {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : R) (x : X) : Prop :=
  ringKrullDim (X.presheaf.stalk x) = 1 ∧ f ∈ (p x).asIdeal

section Spans

variable {R R₁ F F₁ : Type} [CommRing R] [CommRing R₁] [CommRing F] [CommRing F₁]

def spanBy (c : R₁ →+* F₁) (T : Set F₁) : Set F₁ :=
  {v | ∃ (n : ℕ) (r : Fin n → R₁) (t : Fin n → F₁), (∀ i, t i ∈ T) ∧ v = ∑ i, c (r i) * t i}

def LinDisj (c₀ : R →+* F) (c : R₁ →+* F₁) (θ : F →+* F₁) : Prop :=
  ∀ (n : ℕ) (u : Fin n → F), (∀ r : Fin n → R, ∑ i, c₀ (r i) * u i = 0 → r = 0) →
    ∀ r : Fin n → R₁, ∑ i, c (r i) * θ (u i) = 0 → r = 0

def GaussAt (c : R₁ →+* F₁) (q : Ideal R₁) (θ : F →+* F₁) (W : Set F) (W₁ : Set F₁) : Prop :=
  ∀ v : F₁, (∃ d : R₁, d ≠ 0 ∧ c d * v ∈ spanBy c (Set.range θ)) →
    (v ∈ W₁ ↔ ∃ s : R₁, s ∉ q ∧ c s * v ∈ spanBy c (θ '' W))

structure GradedFam (c₀ : R →+* F) (N : ℕ → Set F) : Prop where
  one : (1 : F) ∈ N 0
  zero : ∀ k, (0 : F) ∈ N k
  add : ∀ k, ∀ a ∈ N k, ∀ b ∈ N k, a + b ∈ N k
  smul : ∀ k (r : R), ∀ a ∈ N k, c₀ r * a ∈ N k
  mul : ∀ k l, ∀ a ∈ N k, ∀ b ∈ N l, a * b ∈ N (k + l)

end Spans

structure IsModel {R F : Type} [CommRing R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F) {P : Scheme.{0}} [IsIntegral P]
    (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens) : Prop where
  sep : IsSeparated p
  const : ψ.comp (cst p) = c₀
  affine : ∀ k, 1 ≤ k → ∀ b ∈ N k, IsAffineOpen (Dp k b)
  cover : ∀ z : P, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp k b
  gen : ∀ k, 1 ≤ k → ∀ b ∈ N k, (genericPoint P ∈ Dp k b ↔ b ≠ 0)
  ring : ∀ k, 1 ≤ k → ∀ b ∈ N k, b ≠ 0 → ∀ u : F,
    (∃ v, (∀ z ∈ Dp k b, RegAt z v) ∧ ψ v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m
  mem : ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ z ∈ Dp k b, ∀ l, 1 ≤ l → ∀ a ∈ N l,
    (z ∈ Dp l a ↔ ∃ v, UnitAt z v ∧ ψ v = a ^ k / b ^ l)

def MulAgree {S₁ S₂ P : Scheme.{0}} (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P) : Prop :=
  ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₂ : T ⟶ S₂) (a b : Over.mk t₁ ⟶ H₁) (a' b' : Over.mk t₂ ⟶ H₂),
    a.left ≫ h₁ = a'.left ≫ h₂ → b.left ≫ h₁ = b'.left ≫ h₂ → (a * b).left ≫ h₁ = (a' * b').left ≫ h₂

def OneAgree {S S₁ S₂ P : Scheme.{0}} (s₁ : S₁ ⟶ S) (s₂ : S₂ ⟶ S) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂]
    (h₁ : H₁.left ⟶ P) (h₂ : H₂.left ⟶ P) : Prop :=
  ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₂ : T ⟶ S₂), t₁ ≫ s₁ = t₂ ≫ s₂ →
    (1 : Over.mk t₁ ⟶ H₁).left ≫ h₁ = (1 : Over.mk t₂ ⟶ H₂).left ≫ h₂

def OpenIn {S S₁ P Y : Scheme.{0}} (h : Y ⟶ P) (q : Y ⟶ S₁) (p : P ⟶ S) (s : S₁ ⟶ S) : Prop :=
  ∃ w : h ≫ p = q ≫ s, IsOpenImmersion (pullback.lift h q w)

structure Chart {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (x : S) where

  R : Type
  [cr : CommRing R]
  [reg : IsRegularLocalRing R]
  [dom : IsDomain R]
  complete : IsAdicComplete (maximalIdeal R) R
  charZero : CharZero R

  ξ : Sp R ⟶ S
  centre : ξ (closedPoint R) = x
  etc : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom
  unr : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified

  G : Over (Sp R)
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  y : Sp (FractionRing R) ⟶ X
  hy : y ≫ j = jK R ≫ ξ

  α : pullback G.hom (jK R) ⟶ A.left
  gen : IsGrpPullback ((Over.pullback (jK R)).obj G) A y α

attribute [instance] Chart.cr Chart.reg Chart.dom Chart.grp

abbrev awayMap {R : Type} [CommRing R] (f : R) : Sp (Localization.Away f) ⟶ Sp R :=
  spMap (algebraMap R (Localization.Away f))

structure Setup where

  R : Type
  [cr : CommRing R]
  [dom : IsDomain R]
  [noeth : IsNoetherianRing R]
  [normal : IsIntegrallyClosed R]

  f : R
  hf : f ≠ 0

  A : Over (Sp (Localization.Away f))
  [grp : GrpObj A]
  ab : IsAbelianScheme A
  [int : IsIntegral A.left]

  D : CartierDiv A.left
  amp : AmpleDiv D

  C : ∀ x : Sp R, Chart (awayMap f) A x
  [intC : ∀ x, IsIntegral (C x).G.left]

  ρ : ∀ x, R →+* (C x).R
  hρ : ∀ x, (C x).ξ = spMap (ρ x)
  flat : ∀ x, (ρ x).Flat

  V : ∀ x, (C x).G.left.Opens
  hV : ∀ x (z : (C x).G.left), z ∈ V x ↔ ρ x f ∉ ((C x).G.hom z).asIdeal

  φ : ∀ x, (V x).toScheme ⟶ A.left
  cart : ∀ x, IsPullback (φ x) ((V x).ι ≫ (C x).G.hom) (A.hom ≫ awayMap f) (spMap (ρ x))
  compat : ∀ x (T : Scheme.{0}) (t : T ⟶ pullback (C x).G.hom (jK (C x).R)) (t' : T ⟶ (V x).toScheme),
    t ≫ pullback.fst _ _ = t' ≫ (V x).ι → t ≫ (C x).α = t' ≫ φ x

  θ : ∀ x, A.left.functionField →+* (C x).G.left.functionField
  hθ : ∀ x, PFF (V x).ι (φ x) (θ x)

  D₁ : ∀ x, CartierDiv (C x).G.left
  pull : ∀ x, PPull (V x).ι (φ x) (θ x) D (D₁ x)
  noVert : ∀ x z, Vert (C x).G.hom (ρ x f) z → (D₁ x).IsEqn z 1
  amp₁ : ∀ x, AmpleDiv (D₁ x)

attribute [instance] Setup.cr Setup.dom Setup.noeth Setup.normal Setup.grp Setup.int Setup.intC

namespace Setup

variable (σ : Setup)

def c₀ : σ.R →+* σ.A.left.functionField := cst (σ.A.hom ≫ awayMap σ.f)

def W (x : Sp σ.R) : Set σ.A.left.functionField :=
  {u | ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z (σ.θ x u)}

def N (k : ℕ) : Set σ.A.left.functionField := {u | u ∈ Sec σ.D k ∧ ∀ x, u ∈ σ.W x}

def Common : Prop :=
  ∀ (x x' : Sp σ.R) (Ω : Type) [Field Ω] (u : (σ.C x).R →+* Ω) (u' : (σ.C x').R →+* Ω),
    RingHom.ker u' = maximalIdeal _ → u.comp (σ.ρ x) = u'.comp (σ.ρ x') →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : (σ.C x).R →+* E) (b : (σ.C x').R →+* E)
      (v : E →+* Ω) (H : Over (Sp E)) (_ : GrpObj H) (_ : IsIntegral H.left) (πa : H.left ⟶ (σ.C x).G.left)
      (πb : H.left ⟶ (σ.C x').G.left) (θa : (σ.C x).G.left.functionField →+* H.left.functionField)
      (θb : (σ.C x').G.left.functionField →+* H.left.functionField),
      a.Flat ∧ b.Flat ∧ a.comp (σ.ρ x) = b.comp (σ.ρ x') ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧
      (RingHom.ker u).map a = maximalIdeal E ∧ IsSemiAbelian H ∧ IsGrpPullback H (σ.C x).G (spMap a) πa ∧
      IsGrpPullback H (σ.C x').G (spMap b) πb ∧ PFF (𝟙 _) πa θa ∧ PFF (𝟙 _) πb θb ∧ θa.comp (σ.θ x) = θb.comp (σ.θ x')

end Setup

structure Emb (σ : Setup) where

  P : Scheme.{0}
  [int : IsIntegral P]

  p : P ⟶ Sp σ.R
  sep : IsSeparated p

  ψ : P.functionField →+* σ.A.left.functionField

  ιA : σ.A.left ⟶ P
  cartA : IsPullback ιA σ.A.hom p (awayMap σ.f)
  ffA : PFF (𝟙 _) ιA ψ

  emb : ∀ x, (σ.C x).G.left ⟶ P
  openIn : ∀ x, OpenIn (emb x) (σ.C x).G.hom p (spMap (σ.ρ x))
  ff : ∀ x, PFF (𝟙 _) (emb x) ((σ.θ x).comp ψ)
  onV : ∀ x, σ.φ x ≫ ιA = (σ.V x).ι ≫ emb x

attribute [instance] Emb.int

def Emb.U {σ : Setup} (E : Emb σ) : Set E.P :=
  {z | ∃ (x : Sp σ.R) (y : (σ.C x).G.left), (σ.C x).G.hom y = closedPoint _ ∧ E.emb x y = z}

def Emb.LocGrp {σ : Setup} (E : Emb σ) (g : σ.R) (H : Over (Sp (Localization.Away g))) [GrpObj H] (h : H.left ⟶ E.P) : Prop :=
  Smooth H.hom ∧ QuasiCompact H.hom ∧ IsOpenImmersion h ∧ h ≫ E.p = H.hom ≫ awayMap g ∧ MulAgree H σ.A h E.ιA

def SqDec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L M : LB A.left) : Prop :=
  ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (A ⟶ A)), 1 ≤ N ∧ 1 ≤ a₀ ∧ (∀ i, IsMonHom (β i)) ∧
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 A.left) fun i => (β i).left)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))

def HasExt {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] : Prop :=
  ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e

theorem subset_spanBy {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) (T : Set F₁) : T ⊆ spanBy c T :=
  fun t ht => ⟨1, fun _ => 1, fun _ => t, fun _ => ht, by simp⟩

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def uIdeal (D : Datum p) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

theorem p_mem_uIdeal (D : Datum p) (r : ℤ) : (p : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem sub_mem_uIdeal (D : Datum p) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def IsPIsog {N : ℕ} {s : S ⟶ Sp R} (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  (∃ k : ℕ, c = p ^ k) ∧
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta x ≫ ψ) ∧
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ∧
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

theorem IsPIsog.exists_eq_pow {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : ∃ k : ℕ, c = p ^ k := h.1

theorem IsPIsog.pos {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : 0 < c := by
  obtain ⟨k, rfl⟩ := h.1
  exact pow_pos (Fact.out : p.Prime).pos k

def KilledBy {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over S} (g : T ⟶ o.A) : Prop :=
  ∀ a ∈ v, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1

def IsTj {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S),
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

structure TjCorr {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) where

  Y : Scheme.{0}

  s : Y ⟶ F.X

  t : Y ⟶ F.X
  st : s ≫ F.s = t ≫ F.s

  o : Obj b N (s ≫ F.s)

  o' : Obj b N (s ≫ F.s)
  ms : ObjMap o F.univ s
  mt : ObjMap o' F.univ t

  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ

  wPrime : w.IsPrime

  uLe : uIdeal D r ≤ w

  pReg : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0

  sFin : IsFinite s

  tFin : IsFinite t

  sSurj : Surjective s

theorem KilledBy.one {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) (T : Over S) :
    KilledBy o v (1 : T ⟶ o.A) := fun a _ => by
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
  exact one_comp _

theorem pReg_of_flat {Y : Scheme.{0}} (s : Y ⟶ Sp R) [Flat s] (hR : ∀ a : R, (p : R) * a = 0 → a = 0)
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · have hfl : (s.appLE ⊤ V.1.1 le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ V.1 le_top
    have hp : (p : Γ(Sp R, ⊤)) ∈ nonZeroDivisors Γ(Sp R, ⊤) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro a ha
      let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      refine e.injective ((hR _ ?_).trans (map_zero e).symm)
      rw [← map_natCast e, ← map_mul, ha, map_zero]
    letI := (s.appLE ⊤ V.1.1 le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V.1.1) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Y, V.1.1)) hp
    let ρ : Γ(Y, U) →+* Γ(Y, V.1.1) := (Y.presheaf.map (homOfLE V.2).op).hom
    show ρ f = ρ 0
    refine hreg ?_
    simp only [Algebra.smul_def, map_natCast, map_zero, mul_zero]
    rw [← map_natCast ρ, ← map_mul, hf, map_zero]

theorem pReg_of_isUnit {Y : Scheme.{0}} (s : Y ⟶ Sp R) (hR : IsUnit (p : R))
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  have := hR.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U le_top).hom)
  rw [map_natCast] at this
  exact this.mul_right_eq_zero.1 hf

def IsWOrd {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {k : Type} [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : Prop :=
  CharP k p ∧ w.IsPrime ∧ (p : 𝓞 D.F) ∈ w ∧
    Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1))

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ClassSums
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

structure FPre {O : Type} [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] where

  Y : Type

  ev : Y → A →+* PadicAlgCl p
  ev_le : ∀ y h, ‖ev y h‖ ≤ 1
  ev_lt : ∀ y, ∀ h ∈ maximalIdeal A, ‖ev y h‖ < 1

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  β : ∀ y, LinearMap.BilinForm ℤ (X y)
  bal : ∀ y, β y ∈ balForms bar (X y)
  pos : ∀ y x, x ≠ 0 → 0 < β y x x

  sc : Y → ℝ
  sc_pos : ∀ y, 0 < sc y

attribute [instance] FPre.add FPre.mod FPre.fin FPre.proj FPre.freeZ FPre.finZ

namespace FPre

variable {O : Type} [CommRing O] {bar : O → O} {q p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : FPre bar q p A) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)

def abelian₂ : Prop :=
  ∃ C : ℝ, ∀ y x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Real.exp (-(C * (Φ.sc y * Φ.β y x x))) ≤ ‖Φ.ev y h‖

def IsTerms {Q : Type} (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  (∀ y μ c, ‖t y μ c‖ ≤ Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))) ∧
    ∀ y μ, ∃ c, ‖t y μ c‖ = Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))

def OrbitSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  ∀ (m : ℕ) (a : Fin m × Fin s → Φ.X y₀) (c : Fin m → Q) (e : ℕ), ∃ f : A, ∀ y,
    ∃ h ∈ maximalIdeal A, ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin m × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
      (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ))) < ε) ∧
      ‖Φ.ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤ max ε (‖Φ.ev y h‖ ^ e)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type)
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod O N (k y)) ∧ Φ.IsTerms W t ∧
      Φ.OrbitSums W N₁ N y₀ k t

def Approx (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (e : ℕ), ∃ f : A, ‖Φ.ev y₀ f‖ = Real.exp (-(Φ.sc y₀ * (d * φ.evalZ (Φ.β y₀)))) ∧
    ∀ y, ‖Φ.ev y f‖ ≤ Real.exp (-(Φ.sc y * (d * φ.evalZ (Φ.β y)))) ∨ ∃ h ∈ maximalIdeal A, ‖Φ.ev y f‖ ≤ ‖Φ.ev y h‖ ^ e

def ClassSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [Algebra A B] (𝔷 : Ideal B) : Prop :=
  ∃ (ev' : Φ.Y → B →+* PadicAlgCl p) (f : (Fin s → Φ.X y₀) → Q → B),
    (∀ y a, ev' y (algebraMap A B a) = Φ.ev y a) ∧ (∀ y b, ‖ev' y b‖ ≤ 1) ∧ (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) ∧
    (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧
    (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin s → Φ.X y), ∀ S : Finset (Fin s → Φ.X y),
      (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) →
        ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧
    ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧
      (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod N₁ (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ

end FPre

end GlobalTheory.Poinc
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc

variable {g n : ℕ}

structure Setup (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) where

  o₁ : Type

  Ω₁ : Type
  [ring : CommRing o₁]
  [field : Field Ω₁]
  [alg : Algebra o₁ Ω₁]
  [ar : ArithBase o₁ Ω₁]

  S : ThetaSys o₁ Ω₁

  ρ : S.Real
  big : S.Big

  u : Sp S.R ⟶ F.X
  sharp : SharpOver F W ρ.P u
  gen : ∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X

  M : RatModel o₁ Ω₁
  normal : IsNormalScheme M.Z

  π : M.Z ⟶ Z
  fin : IsFinite π
  comp : M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i

  one_le : 1 ≤ g

  three_le : 3 ≤ n

  odd : Odd n

  z : Z ⟶ Sp (cycAway n)

  proj : IsProjOver z

  normalZ : IsNormalScheme Z

  imm : IsOpenImmersion i

  thetaSetup_structureMap_comp : i ≫ z = F.s

  dense : Dense (Set.range i)

  e8 : IsE8 W

  thetaInt : ThetaInt F W i

  κ : cycAway n →+* o₁

  base : spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ)

attribute [instance] Setup.ring Setup.field Setup.alg Setup.ar

structure CTrait {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i)
    (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) where

  y : Sp (OO p) ⟶ X₁.M.Z
  cen : y (cPt p) = z₁

  T : Trait F

  ι : FractionRing T.V →+* PadicAlgCl p
  int : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))
  comm : gPt p ≫ y ≫ X₁.π = spMap ι ≫ T.y ≫ i

variable {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

namespace Setup

variable (X₁ : Setup F W i)

theorem div : X₁.M.HasDiv X₁.S.th :=
  X₁.thetaInt X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp


include X₁ in
theorem posW : PosW W := X₁.e8.1


include X₁ in
theorem diag_pos (a : Fin 8) : 0 < W a a := by
  have := X₁.e8.1.diag_pos (i := a)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
  have h2 : (0 : ℤ) < W a a + W a a := by exact_mod_cast this
  omega

theorem isProper_compactificationMap : IsProper X₁.z := ((isProjOver_iff_isProper_and_exists_isAmpleLB X₁.z).1 X₁.proj).1

theorem s_comp : X₁.M.s ≫ spMap X₁.κ = X₁.π ≫ X₁.z := by
  refine ext_of_isDominant X₁.M.pt ?_
  rw [← Category.assoc, X₁.M.pt_s, ← Category.assoc, X₁.comp, Category.assoc, Category.assoc, X₁.thetaSetup_structureMap_comp, X₁.base]
  exact (Spec.map_comp (CommRingCat.ofHom X₁.κ) (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))).symm

theorem projM : IsProjOver X₁.M.s := by
  haveI := X₁.fin
  obtain ⟨h1, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB X₁.z).1 X₁.proj
  haveI : IsProper (X₁.M.s ≫ spMap X₁.κ) := by rw [s_comp]; infer_instance
  haveI : IsProper X₁.M.s := IsProper.of_comp X₁.M.s (spMap X₁.κ)
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, _, hL.pull_of_isFinite X₁.π⟩

end Setup

def CTrait.sc {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : ℝ :=
  -Real.log ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖

def CTrait.val {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (a : X₁.M.Z.presheaf.stalk z₁) : PadicAlgCl p :=
  X₁.M.val (gPt p ≫ c.y) (X₁.M.stalkHom z₁ a)

namespace CTrait

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc c.y z₁ (specializes_of_eq c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : c.val a = (c.valInt a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype c.y (specializes_of_eq c.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖c.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (c.valInt a : PadicAlgCl p) ≤ 1 := (c.valInt a).2
  exact_mod_cast h

theorem norm_uniformiser_pos (c : CTrait X₁ p z₁) : 0 < ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero c.ι).2 fun h =>
    c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h))

theorem scale_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have h1 := c.norm_uniformiser_pos
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h => by simp [h] at h1
  have h2 : ‖c.ι x‖ < 1 := by
    by_contra h
    have : ‖c.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (c.int _).1 this
    refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)

theorem exp_neg_sc_mul (c : CTrait X₁ p z₁) (a : ℕ) :
    Real.exp (-(c.sc * a)) = ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ a := by
  rw [CTrait.sc, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log c.norm_uniformiser_pos]

end CTrait

def FPre.Matches {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)) :
    Prop :=
  ∀ c : CTrait X₁ p z₁, ∃ y : Φ.Y, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
    ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)

def ApproxAt (X₁ : Setup F W i) (φ : InvFun ℤ) (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c₀ : CTrait X₁ p z₁) (e : ℕ), ∃ f : X₁.M.Z.presheaf.stalk z₁,
    ‖c₀.val f‖ = Real.exp (-(c₀.sc * (d * φ.evalZ c₀.T.β))) ∧ ∀ c : CTrait X₁ p z₁,
      ‖c.val f‖ ≤ Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ∨
        ∃ h ∈ IsLocalRing.maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖c.val f‖ ≤ ‖c.val h‖ ^ e

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Half (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T ⟶ D.P.A) (1 : T ⟶ D.P.A)).left z J J' = 1) ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)) =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

theorem Half.refines {Q : Data R} {ρ : R →+* R'} {D : DegPre R'} {e : D.X ≃+ Q.X} (h : Half Q ρ D e fun _ _ => 1) :
    Refines Q ρ D e := by
  obtain ⟨β, β₂, w, h₁, h₂, h₃, -, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have := h₅ κ hκ a b z J J' hJ hJ'
  rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this

def rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) : DegPre R :=
  { D with
    psi := fun χ => GlobalTheory.UU.scaleGen (unitOn (g χ)) (D.psi χ)
    psi_gen := fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ) }

def EvenDefect (D : DegPre R) (h : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ z J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (h χ)) * val (D.psi χ) (𝟙 _) z J

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def Base (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop := AdmBase R (maximalIdeal R) ∧ CharZero R

def FinExt {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') : Prop :=
  AdmBase R' (maximalIdeal R') ∧ Function.Injective ρ ∧ ρ.Finite

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def Has (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R))),
    IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R) D A G)

def HasFin (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')),
    FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Has D'

def EvenOn {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (Q₀ : GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
    GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧ ∃ σ : GlobalTheory.UU.CubTriv P₀.c Q₀.i, σ.Even

end

structure Modif (R : Type) [CommRing R] [IsDomain R] where

  S : Scheme.{0}

  π : S ⟶ Sp R
  proper : IsProper π
  integral : IsIntegral S

  gp : Sp (FractionRing R) ⟶ S
  gp_π : gp ≫ π = jK R
  dominant : IsDominant gp

def Modif.self (R : Type) [CommRing R] [IsDomain R] : Modif R where
  S := Sp R
  π := 𝟙 _
  proper := inferInstance
  integral := inferInstance
  gp := jK R
  gp_π := Category.comp_id _
  dominant := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]; exact bot_le)⟩

section

variable {R : Type} [CommRing R] [IsDomain R]

def IsFactor (D D' : DegPre R) : Prop :=
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  ∃ (O : Type) (_ : Ring O) (_ : StarRing O) (_ : Module O D'.X) (o : D'.OAct O) (e f : O)
    (inc : D.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D.P.A) (xi : D.X →+ D'.X) (xp : D'.X →+ D.X)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)),
    e * e = e ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o.onB.act e ∧
    (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = e • z) ∧ (∀ y, D'.c (xi y) = D.c y ≫ inc) ∧
    (Function.Injective (fun y => star e • f • xi y) ∧ ∀ z, ∃ y, star e • z = star e • f • xi y) ∧ w.IsGen ∧
    ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
          val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

def PelOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dm : Datum H) (D : DegPre R)
    [Module (𝓞 E) D.X] (o : letI := H.starRing; D.OAct (𝓞 E)) : Prop :=
  letI := H.starRing
  Dm.p = Dm.q ∧ 1 ≤ Dm.p ∧ TraceFormTwistIso D o H.w0 ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
      (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct o.onB.toRingAct)
        (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧ n + Module.finrank (𝓞 E) D.X = Dm.p) ∧
      ∀ ζ : ℕ → Fˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) →
        ∃ I : TateIsoQ Dm D o F, I.ζ = ζ

end

structure LabCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)

  n : ℕ
  n_prime : n.Prime
  n_odd : Odd n
  n_unit : IsUnit (n : R)

  lab : ∀ j : ℕ, QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j) →
    (TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G')
      (hD : IsPullDeg (io.comp φ) D.toPre D'.toPre),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W') F] [Algebra (FractionRing R) F]
        (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
        (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W') F (algebraMap W' _ (io (φ r)))) →
        ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j)) (p₁ : QkPt D.toPre F (n ^ j))
          (p' : QkPt D'.toPre F (n ^ j)) (x' : TFK (R := W') F ⟶ A'.A),
          QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF (io.comp φ) hD F p₁.g p'.g →
          x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK W') ≫ β = spMap em.toRingHom ≫ (lab j p).left ≫ α →
          QkToAkU U'.toUnifPre F (n ^ j) p' x'

attribute [instance] LabCover.grp LabCover.comm

section Inhabitants

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem base_powerSeries : Base (PowerSeries ℚ) := by
  have hc : IsAdicComplete (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  exact ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, algebraRat.charZero _⟩

end Inhabitants

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.Poinc

structure ATrait (X : Scheme.{0}) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V
  ϖ : V
  irr : Irreducible ϖ
  ξ : Sp V ⟶ X

attribute [instance] ATrait.ring ATrait.dom ATrait.dvr ATrait.char

def ATrait.GenIn {X : Scheme.{0}} (T : ATrait X) (U : Set X) : Prop := Set.range (jK T.V ≫ T.ξ) ⊆ U

def ATrait.HasOrd {X : Scheme.{0}} (T : ATrait X) {x : X} (h : T.ξ (closedPoint T.V) ⤳ x) (f : X.presheaf.stalk x)
    (a : ℕ) : Prop :=
  Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom ((X.presheaf.stalkSpecializes h).hom f)} = Ideal.span {T.ϖ ^ a}

def ATrait.CentredAt {X : Scheme.{0}} (T : ATrait X) (η : X) (e : ℕ) : Prop :=
  T.ξ (closedPoint T.V) = η ∧ Function.Injective (Scheme.stalkClosedPointTo T.ξ).hom ∧ 1 ≤ e ∧
    ∃ h : T.ξ (closedPoint T.V) ⤳ η, (maximalIdeal (X.presheaf.stalk η)).map
      ((Scheme.stalkClosedPointTo T.ξ).hom.comp (X.presheaf.stalkSpecializes h).hom) = Ideal.span {T.ϖ ^ e}

def EqAt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : EffCartierData M.Z) (x : M.Z) (f : Ω) :
    Prop := ∃ i, x ∈ D.U i ∧ f = valF M.pt (D.U i) (D.f i)

def NonUnitAt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) (h : Ω) : Prop :=
  h ∈ M.O z ∧ (h = 0 ∨ h⁻¹ ∉ M.O z)

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.RepFamModel
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem objMap_refl {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) :
    Nonempty (ObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }⟩

variable {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
  {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

end GlobalTheory.UPel.HT.RepFamModel
end
end
