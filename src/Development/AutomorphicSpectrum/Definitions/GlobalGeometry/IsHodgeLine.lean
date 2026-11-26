module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev CMType (H : Host E) : Type := {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}

def labelEmb (c : Coeff l) : CMType H ⊕ CMType H → (𝓞 E →+* c.F)
  | .inl τ => (τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)
  | .inr τ => ((τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)).comp (H.bar : 𝓞 E →+* 𝓞 E)

abbrev labelRk (D : Datum H) : CMType H ⊕ CMType H → ℕ := Sum.elim (fun _ => D.p) (fun _ => D.q)

def htLabel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) : CMType H ⊕ CMType H → Lat ξ Li
  | .inl τ => M.htW L n ρ (σ (.inl τ)) (differentIdeal ℤ (𝓞 E))
  | .inr τ => M.htDual L n ρ (σ (.inr τ))

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure HodgeCpt (Y : Model Xo c β) (S : Finset ℕ) {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of Ω) ⟶ X
  all : ∀ q : X, genPt ξ ⤳ q
  tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩
  normal : IsNormalScheme X

  f : X ⟶ Y.X

  Ω₀ : Type
  [fld₀ : Field Ω₀]

  ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X
  gen₀ : IsCptGen ξ₀

  cst : c.F →+* Ω
  cst_over : ξ ≫ f ≫ Y.s = spMap (cst.comp β)

  fn : Ω₀ →+* Ω
  fn_over : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f fn

  t : SAB H X
  m : SABMap t Y.t f

  Li : Type
  [acg : AddCommGroup Li]
  [mod : Module Ω Li]
  M : LieModel t.G ξ Li

  ρ : 𝓞 E →+* Module.End Ω Li
  act : M.IsActOf t.act.act ρ
  S_prime : ∀ p ∈ S, p.Prime

  R : ℕ → ℕ
  R_ge : ∀ p ∈ S, 4 ≤ R p
  tors : ∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)
  vb : ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s)))
      fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
    (eigSp ρ (cst.comp (labelEmb c s)))

attribute [instance] HodgeCpt.fld₀ HodgeCpt.acg HodgeCpt.mod

namespace HodgeCpt

variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def emb (s : CMType H ⊕ CMType H) : 𝓞 E →+* Ω := 𝔐.cst.comp (labelEmb c s)

def Vgen (s : CMType H ⊕ CMType H) : Submodule Ω 𝔐.Li := eigSp 𝔐.ρ (𝔐.emb s)

def dR (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := 𝔐.M.eigLat 𝔐.ρ (𝔐.emb s)

def HT (p : ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := htLabel 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ 𝔐.emb s

def V (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := Lat.patch S (𝔐.dR s) fun p => 𝔐.HT p s

def IsCover (d : ℕ) : Prop :=
  0 < d ∧ letI := 𝔐.fn.toAlgebra; Module.finrank 𝔐.Ω₀ Ω = d

def Interior {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ 𝔐.X) : Prop :=
  centre z ∈ abLocus 𝔐.t.G

structure Flag where

  b : ∀ s, Fin (labelRk D s) → 𝔐.Li
  sub : ∀ s, (𝔐.V s).IsFlagVBOn Set.univ (b s)

  Li₀ : Type
  [acg : AddCommGroup Li₀]
  [mod : Module 𝔐.Ω₀ Li₀]
  M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀

  j : Li₀ →+ 𝔐.Li
  j_pt : ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left

  V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀
  V₀_mem : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s

  deg : ℕ
  generic : letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b deg

attribute [instance] Flag.acg Flag.mod

variable {𝔐}

def rootIdx (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : Σ s, Fin (labelRk D s) :=
  if h : (r.2 : ℕ) < D.p then ⟨.inl r.1, ⟨r.2, h⟩⟩
  else ⟨.inr r.1, ⟨D.p + D.q - 1 - r.2, by have := r.2.2; show _ < D.q; omega⟩⟩

def rootSgn (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : ℤ := if (r.2 : ℕ) < D.p then 1 else -1

def Flag.rootLat (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) : Lat 𝔐.ξ Ω :=
  Lat.tens (fun _ : Unit => (𝔐.V (rootIdx D r).1).gr (Fl.b (rootIdx D r).1) (rootIdx D r).2) fun _ => rootSgn D r

def Flag.RootLines (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) : Prop :=
  ∀ r, (Fl.rootLat r).IsDegOn Set.univ y (xdeg r) (e r)

def Flag.IsHodgeLine [∀ k, Fintype (J k)] (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (e₀ : Ω)
    (A : HermLine J) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
    ∀ t ν, 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V (rootIdx D r).1) (Fl.b (rootIdx D r).1) (rootIdx D r).2 z t ν →
      SecNorm 𝔐.ξ y A e₀ z w (t ^ rootSgn D r) (ν ^ rootSgn D r)

end HodgeCpt

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R]

def IsComb {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G))
    (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigVec {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    (v : epsAt x ⟶ G) : Prop :=
  IsTanAt G x v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsMul (τ a)) ≫ v.left

def IsEigFrame {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigVec act x τ (v i)) ∧ ∀ w, IsEigVec act x τ w → ∃! c : Fin n → R, IsComb c v w

def IsHodgeGram (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) {n : ℕ} (v : Fin n → (epsAt x ⟶ G))
    (Γ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ G.left) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
    (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin n → Fin Q.g → ℂ),
    IsGrpPullback Q.A G x ψ ∧ LBIso (L.pull ψ) Q.L ∧ u.IsAH Hm χ ∧
      (∀ i, (v' i).left ≫ ψ = (v i).left ∧ u.IsDiff (W i) (v' i)) ∧ ∀ i j, Γ i j = Real.pi * hermForm Hm (W i) (W j)

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauIn {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F :=
  ((τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E) :)

def sesq (D : Datum H) (x y : D.La) : E :=
  ∑ k, (D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k

def tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (z : Fin g → ℂ) : Fin g → ℂ :=
  open Classical in fun k => if ty k = τ then z k else 0

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

def IsHolPts {R : Type} [CommRing R] {n : ℕ} (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) : Prop :=
  IsOpen B ∧ ∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B

structure FamExp {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {g n : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) where

  ex : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)
  add : ∀ b ∈ B, ∀ z w, ex b (z + w) = ex b z * ex b w
  hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left)
  diff : ∀ b ∈ B, ∀ a : Fin g, IsDerivAt0 (fun z => (ex b z).left) (Pi.single a 1)
    (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)
  log : ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (N : ℕ) (f : Fin N → Γ(G.left, V))
    (L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)), ⊤ ≤ (ex b₀ 0).left ⁻¹ᵁ V ∧
    AnalyticAt ℂ L (b₀, fun j => valAt' (ex b₀ 0).left V (f j)) ∧
    (∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0),
      L (bz.1, fun j => valAt' (ex bz.1 bz.2).left V (f j)) = bz.2) ∧
    ∀ᶠ p : (Fin n → ℂ) × (Fin N → ℂ) in 𝓝 (b₀, fun j => valAt' (ex b₀ 0).left V (f j)),
      ∀ x : Over.mk (spMap (ψ p.1)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, valAt' x.left V (f j) = p.2 j) →
        x = ex p.1 (L p)

def FamExp.per {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) (b : Fin n → ℂ) : Set (Fin g → ℂ) := {z | e.ex b z = 1}

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
