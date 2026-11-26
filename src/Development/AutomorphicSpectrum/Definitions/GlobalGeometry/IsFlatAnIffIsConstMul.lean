module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev CFn (Xo : Moduli D l) (c : Coeff l) : Type := ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → ℂ

variable {Xo : Moduli D l} {c : Coeff l}

def IsFlatAn (U : Set (Xo.XF c)) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) {σK : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ σ y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ' (sesq (FU.Di i) (e m) (e n)) = B j n) →
    Φ y v w * (Matrix.fromRows C Fm).det = ρ

structure IsUnitAn (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) : Prop where

  ne : ∀ y v w, IsFramed Set.univ τ σ y v w → Φ y v w ≠ 0

  chg : ∀ y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) ℂ) (B : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsFramed Set.univ τ σ y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → Φ y v' w' * A.det = Φ y v w * B.det

  norm : ∀ y v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖Δ.det‖

  hol : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G))
    (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ))
    (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B →
    (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) →
    (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧
      (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧
      ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) →
    DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B

def ExtendsUnitAt {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} (s : X ⟶ Sp K) (σ : K →+* ℂ) (ξ : Sp Ω ⟶ X)
    (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (t : Ω) (x : Sp ℂ ⟶ X) : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
    (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x →
    ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧
      ∀ b ∈ B ∩ Metric.ball b₀ ε, ⊤ ≤ y b ⁻¹ᵁ W → ∀ r : ℂ, ValAt ξ (y b) t r → F (y b) = h b * r

variable {O : Type} [CommRing O] {β : O →+* c.F}

def SameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : epsAt (under y) ⟶ Xo.univ.t.G)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : Prop :=
  ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left

theorem exists_sameVec_left (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : ∃ v, SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v'.left ≫ Y.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w v'
  refine ⟨Over.homMk (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ?_, hq.lift _ _ hv, hq.lift_snd _ _ _, rfl,
    hq.lift_fst _ _ _⟩
  have : (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap F (DualNumber F)) ≫ y ≫ pullback.fst _ _ := by
    rw [Category.assoc, hp.w, ← Category.assoc, hq.lift_snd, Category.assoc]
  exact this

theorem SameVec.unique {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v₁ v₂ : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v v₁) (h₂ : SameVec Y y v v₂) : v₁ = v₂ := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← c₁, ← c₂, this]

theorem SameVec.unique_left {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v₁ v₂ : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v₁ v') (h₂ : SameVec Y y v₂ v') : v₁ = v₂ := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← b₁, ← b₂, this]

def Represents (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ Y.X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel Y.t.G ξ V) (a : ⋀[Ω]^D.p V) (b : ⋀[Ω]^D.q V)
    (φ : FrameFn Xo c) : Prop :=
  ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (b₁ : Fin D.p → V) (b₂ : Fin D.q → V) (α κ : Ω), IsFramed U τ βF y v w →
    a = α • exteriorPower.ιMulti Ω D.p b₁ → b = κ • exteriorPower.ιMulti Ω D.q b₂ →
    (∀ i, ∃ v', M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') →
    (∀ j, ∃ w', M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') →
    ValAt ξ (y ≫ Y.j) (α / κ) (φ F y v w)

structure CptOver (Y : Model Xo c β) (U : Set (Xo.XF c)) where

  Ω : Type
  [field : Field Ω]

  ξ₀ : Sp Ω ⟶ Xo.XF c

  inc : c.F →+* Ω

  over_inc : ξ₀ ≫ pullback.snd _ _ = spMap inc

  gen : IsCptGen (ξ₀ ≫ Y.j)

  closure : ∀ u : Xo.XF c, u ∈ U ↔ genPt ξ₀ ⤳ u

  V : Type
  [acg : AddCommGroup V]
  [mod : Module Ω V]

  M : LieModel Y.t.G (ξ₀ ≫ Y.j) V

  ρ : 𝓞 E →+* Module.End Ω V

  act : M.IsActOf Y.t.act.act ρ

attribute [instance] CptOver.field CptOver.acg CptOver.mod

def CptOver.eig {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) : Lat (Z.ξ₀ ≫ Y.j) Z.V :=
  Z.M.eigLat Z.ρ (Z.inc.comp (tauIn c τ))

def CptOver.genFib {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Set (Cpt (Z.ξ₀ ≫ Y.j)) :=
  {x | x.1 ∈ Set.range (pullback.fst Y.s (spMap β))}

def FlatOnModel {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop :=
  IsLineFn U τ φ ∧ ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧ Represents Y U τ Z.M a b φ

theorem FlatOnModel.isLineFn {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : IsLineFn U τ φ := h.1

theorem FlatOnModel.exists_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧
      Represents Y U τ Z.M a b φ := h.2

theorem FlatOnModel.of_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} {a : ⋀[Z.Ω]^D.p Z.V} {b : ⋀[Z.Ω]^D.q Z.V} (hφ : IsLineFn U τ φ)
    (hg : IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib)
    (hr : Represents Y U τ Z.M a b φ) : FlatOnModel Z τ φ := ⟨hφ, a, b, hg, hr⟩

theorem CptOver.genPt_mem {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : genPt Z.ξ₀ ∈ U :=
  (Z.closure _).2 specializes_rfl

def CptOver.IsGeom {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Prop :=
  ∀ x : Z.Ω, (∃ f : Polynomial c.F, f ≠ 0 ∧ f.eval₂ Z.inc x = 0) → x ∈ Set.range Z.inc

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg)

noncomputable section

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

structure IsPreFamily (x : (Σ k, J k) → Ω) (p : ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O)
    (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
    (RC : Subalgebra O C), IsTestPt p (chartRing O (mseg x) c) RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      ((D c).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

def coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) : AddSubgroup (Fin m → Ω) :=
  ⨅ (q : Cpt ξ) (_ : InChart ξ (mseg y) c q) (_ : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q),
    (L q).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom

def IsFamilyOf (y : (Σ k, J k) → Ω) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) (L L' Lc Lc' : Sg → Lat ξ V)
    (b : ∀ τ, Fin (r τ) → V) (bc : ∀ τ, Fin (s τ) → V) : Prop :=
  ∀ c, mseg y c ≠ 0 → ∀ τ, (D c).lie τ = coordLat O y (L τ) (b τ) c ∧ (D c).W τ = coordLat O y (L' τ) (b τ) c ∧
    (D c).om τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc τ) (bc τ) c) ∧
    (D c).omHT τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc' τ) (bc τ) c)

namespace Fam


omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem mem_coordLat_iff (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) (a : Fin m → Ω) :
    a ∈ coordLat O y L b c ↔ ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) →
      ∑ i, a i • b i ∈ L q := by
  simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]



omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in
theorem chartRing_le_regAt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) (h1 : InChart ξ (mseg y) c q)
    (h2 : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h1.2 j
  | algebraMap o => exact h2 o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht





end Fam

end

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def HodgeCpt.OmVB {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) : Prop :=
  ∀ p ∈ S, (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q}
      (labelRk D s) ⊤

def IsTowerOf (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) : Prop :=
  ∃ o : TowerOrigin Y T, ∀ B a, (o.Or B a).𝔐.OmVB

def SplitComps {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω), IsCptGen ξ →
    ξ ≫ Y.s = spMap (cst.comp β) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem bar_eq (H : Host E) (a : 𝓞 E) : RingOfIntegers.mapRingEquiv (cmConj E) a = H.bar a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq a]
  rfl

theorem overZp_of_inFibre {p : ℕ} (hp : p.Prime) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) : OverZp 𝔐 p q := by
  intro r hr hrq
  by_contra hne
  have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
    IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
      (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
  have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
    intro m hm hu
    apply hm
    obtain ⟨u, hu'⟩ := hu
    have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
      have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
      simpa [hu'] using h2
    have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, natCast_mem _ m, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
  · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)

variable {𝔐} {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]
  {Dc Dc' : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}

end GlobalTheory.CompanionTheory.Ar.HT.ModelTest
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BadExists
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}

theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
end
end
