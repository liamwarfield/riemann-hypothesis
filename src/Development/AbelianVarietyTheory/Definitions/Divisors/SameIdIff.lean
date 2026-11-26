module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} (A : Over S)

def Same {T U Y : Over S} (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) : Prop :=
  LBIso (ev N (fst A Y) (snd A Y ≫ y)) (ev M (fst A Y) (snd A Y ≫ u))

def Inj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (Y : Over S) (u u' : Y ⟶ U), Same A M M u u' → u = u'

def FibInj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (Y : Over S) (_ : Y ⟶ Over.mk s) (u u' : Y ⟶ U),
    Same A M M u u' → u = u'

def ChartAt {U T : Over S} (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) : Prop :=
  ∃ W : T.left.Opens, ∀ (Y : Over S) (y : Y ⟶ T), (∃ u : Y ⟶ U, Same A N M y u) ↔ ∀ z, y.left z ∈ W

structure Good (g : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop where
  proper : IsProper f
  smooth : SmoothOfRelativeDimension g f
  conn : GeometricallyConnected f

def FinAff (X : Scheme.{0}) : Prop :=
  ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

def DimLe (B : Over S) : Prop :=
  ∀ (g : ℕ) (T : Scheme.{0}) (t : T ⟶ S),
    SmoothOfRelativeDimension g (pullback.snd A.hom t) → SmoothOfRelativeDimension g (pullback.snd B.hom t)

variable [GrpObj A]

structure Fam {T : Over S} (N : LB (A ⊗ T).left) : Prop where
  isLB : N.IsLB
  add : IsAdditive N

structure IsChart {U : Over S} (M : LB (A ⊗ U).left) : Prop where
  fam : Fam A M
  inj : Inj A M
  chart : ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N

structure Rep {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) : Prop where
  fam : Fam A P
  univ : ∀ (T : Over S) (t : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N →
    ∃! x : T ⟶ B, x ≫ b = t ∧ LBIso N (ev P (fst A T) (snd A T ≫ x))

def HasRep (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left

def HasRepAF (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left ∧ FinAff B.left

def LiftAt (g : ℕ) {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) (x : B.left) : Prop :=
  ∃ (U : Over S) (M : LB (A ⊗ U).left) (j : U ⊗ S' ⟶ B), Fam A M ∧ SmoothOfRelativeDimension g U.hom ∧
    j ≫ b = snd U S' ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left ∧ Same A M P (fst U S') j

variable {A}


omit [GrpObj A] in
theorem same_id_iff {T U : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (u : T ⟶ U) : Same A N M (𝟙 T) u ↔ LBIso N (ev M (fst A T) (snd A T ≫ u)) := by
  rw [Same, ← cls_eq_iff (pull_isLB hN _) (pull_isLB hM _), ← cls_eq_iff hN (pull_isLB hM _), cls_ev hN, evc,
    Category.comp_id, lift_fst_snd, Over.id_left, pull_id]


omit [GrpObj A] in
theorem same_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (y : Y ⟶ T) (u : Y ⟶ U) :
    Same A N M y u ↔ evc hN (fst A Y) (snd A Y ≫ y) = evc hM (fst A Y) (snd A Y ≫ u) :=
  (cls_eq_iff (pull_isLB hN _) (pull_isLB hM _)).symm

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

section Generic

variable {G : Type} [Group G]

def twCent (θ : G →* G) (δ : G) : Subgroup G where
  carrier := {g | g * δ = δ * θ g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at *
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv] at *
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]

def TwCl (θ : G →* G) : Type := Quot fun x y : G => ∃ g, y = g⁻¹ * x * θ g

def TwCl.rep {θ : G →* G} (c : TwCl θ) : G := Quot.out c

def rStab {H : Type} [Group H] (u : H → ℂ) : Subgroup H where
  carrier := {k | ∀ x, u (x * k) = u x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha x
    rw [← ha (x * a⁻¹), inv_mul_cancel_right]

def avg {H : Type} [Group H] (u : H → ℂ) : ℂ := ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out

def levOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (A : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ K', f q.out • (ρ q.out ∘ₗ A)

def twTr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (A : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' then
    LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) else 0

variable [TopologicalSpace G]

def cptPart (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}

def twOrb (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G),
    (((twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
      avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def clSum (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ) (f : G → ℂ) : ℂ :=
  ∑ᶠ c : TwCl θ, if c.rep ∈ S then wt c.rep * twOrb θ K c.rep f else 0

def mass (θ : G →* G) (Γ : Subgroup G) (δ : G) : ℂ :=
  (Nat.card (DoubleCoset.Quotient (Γ.subgroupOf (twCent θ δ) : Set (twCent θ δ))
      ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ) : Set (twCent θ δ))) : ℂ) /
    (Nat.card (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) : ℂ)

def IsHecke (K' : Subgroup G) (f : G → ℂ) : Prop :=
  HasCompactSupport f ∧ ∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x

def IsLevel (θ : G →* G) (K K' : Subgroup G) : Prop := IsOpen (K' : Set G) ∧ K' ≤ K ∧ ∀ k ∈ K', θ k ∈ K'

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Pl (E : Type) [Field E] [NumberField E] : Type := HeightOneSpectrum (𝓞 E)

abbrev GLw (n : ℕ) (w : Pl E) : Type := GL (Fin n) (w.adicCompletion E)

def IsSection (S : Set (Pl E)) : Prop :=
  ∀ w : Pl E, ∃! u, u ∈ S ∧ u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))

def cj (w : Pl E) : w.adicCompletion E →+* w.adicCompletion E :=
  if h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) then h.choose else RingHom.id _

def thL (n : ℕ) (w : Pl E) : GLw n w →* GLw n w := if IsSplitAt w then MonoidHom.id _ else thetaGL n (cj w)

def nrmL (n : ℕ) (w : Pl E) (y : GLw n w) : GLw n w := if IsSplitAt w then y else y * thetaGL n (cj w) y

def thE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : GL (Fin n) E →* GL (Fin n) E :=
  thetaGL n (IsCMField.complexConj E).toRingEquiv.toRingHom

def thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : GL (Fin n) (Af E) →* GL (Fin n) (Af E) :=
  thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv)

def ratF (E : Type) [Field E] [NumberField E] (n : ℕ) : GL (Fin n) E →* GL (Fin n) (Af E) :=
  GeneralLinearGroup.map (algebraMap E (Af E))

def locEl (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) : GLw n w :=
  GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (if IsSplitAt w then δ * thE E n δ else δ)

def Ell (E : Type) [Field E] (n : ℕ) : Set E[X] :=
  {P | P.Monic ∧ P.natDegree = n ∧ P.Separable ∧ ∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1}

def kap (P : E[X]) : ℂ :=
  if h : ∃ δ : GL (Fin P.natDegree) E, (δ * thE E _ δ).val.charpoly = P then
    mass (thF E _) (ratF E _).range (ratF E _ h.choose) /
      2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors P) else 0

def chAt {n : ℕ} (lam : DomWeight n) (Q : ℂ[X]) : ℂ :=
  if h : ∃ g : GL (Fin n) ℂ, g.val.charpoly = Q then
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam h.choose) else 0

def chW {n : ℕ} (lam : InfinitePlace E → DomWeight n) (P : E[X]) : ℂ :=
  ∏ v : InfinitePlace E, (starRingEnd ℂ) (chAt (lam v) (P.map v.embedding))

def stTw (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X]) (φ : GLw n w → ℂ) : ℂ :=
  clSum (thL n w) (GlobalTheory.LFun.KGL w (n := n)) {y | (nrmL n w y).val.charpoly = Q} 1 φ

def stTw2 (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ) : ℂ :=
  clSum ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂} 1 φ

def UL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := if IsSplitAt w then ⊤ else UJ (cj w) 1

def KL (n : ℕ) (w : Pl E) : Subgroup (UL n w) := (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (UL n w)

def kapSign (n : ℕ) (w : Pl E) (Q₁ : (w.adicCompletion E)[X]) (γ : GLw n w) : ℂ :=
  if IsSplitAt w then 1 else
    let V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁))
    (-1) ^ ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E) V₁ i).1 k) * (Module.finBasis (w.adicCompletion E) V₁ j).1 k).det

def kapOrb (n : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (f : UL n w → ℂ) : ℂ :=
  clSum (MonoidHom.id _) (KL n w) {γ | γ.1.val.charpoly = Q₁ * Q₂} (fun γ => kapSign n w Q₁ γ.1) f

structure Term (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type 1 where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  P : ∀ w : Pl E, SmIrr (GLw n w)
  A : ∀ w : Pl E, (P w).V →ₗ[ℂ] (P w).V
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  iso : ∀ w, Nonempty ((P w).ρ.Equiv (locProd h w (σ · w)))
  bij : ∀ w, Function.Bijective (A w)
  split : ∀ w, IsSplitAt w → A w = LinearMap.id
  inter : ∀ w g, A w ∘ₗ (P w).ρ g = (P w).ρ (thL n w g) ∘ₗ A w
  unit : ∀ᶠ w in cofinite, twTr (P w).ρ (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n))
    ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)).indicator 1) (A w) = 1

variable {n : ℕ}

abbrev Term.rep (t : Term E n) (w : Pl E) : Representation ℂ (GLw n w) (t.P w).V := (t.P w).ρ

def IsLevelFam {H : Pl E → Type} [∀ w, Group (H w)] [∀ w, TopologicalSpace (H w)] (θ : ∀ w, H w →* H w)
    (K K' : ∀ w : Pl E, Subgroup (H w)) : Prop :=
  (∀ w, IsLevel (θ w) (K w) (K' w)) ∧ ∀ᶠ w in cofinite, K' w = K w

def IsTest {H : Pl E → Type} [∀ w, Group (H w)] [∀ w, TopologicalSpace (H w)] (K K' : ∀ w : Pl E, Subgroup (H w))
    (φ : ∀ w, H w → ℂ) : Prop :=
  (∀ w, IsHecke (K' w) (φ w)) ∧ ∀ᶠ w in cofinite, φ w = (K w : Set (H w)).indicator 1

abbrev atPl (w : Pl E) (P : E[X]) : (w.adicCompletion E)[X] := P.map (algebraMap E (w.adicCompletion E))

def RegAt2 (a b : ℕ) (w : Pl E) (φ : GLw a w × GLw b w → ℂ) : Prop :=
  ∀ y, φ y ≠ 0 → ((nrmL a w y.1).val.charpoly * (nrmL b w y.2).val.charpoly).Separable

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : Pl E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

def spec {ι : Type} [Fintype ι] (S : Set (Pl E)) (t : ι → Term E n) (C : ι → ℂ) (K' : ∀ w : Pl E, Subgroup (GLw n w))
    (φ : ∀ w : Pl E, GLw n w → ℂ) : ℂ :=
  ∑ i, C i * ∏ᶠ w ∈ S, twTr ((t i).rep w) (GlobalTheory.LFun.KGL w (n := n)) (K' w) (φ w) ((t i).A w)

def IsCompU (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (σ : SmIrr (UL n w)) : Prop :=
  ∃ p : locU n w →* UL n w, (∀ x, (p x).1 = cLoc w x.1) ∧ IsCompAlong π (locU n w) p σ.ρ

def HasLevel (S : Set (Pl E)) (π : Submodule ℂ (UA E n → ℂ)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Prop :=
  ∃ φ ∈ π, φ ≠ 0 ∧ ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ

def geomU (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  ∑ a ∈ Finset.range (n + 1), ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
    kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)

def USide : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
    ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)) (σ : ι → ∀ w : Pl E, SmIrr (UL n w)),
      (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ HasLevel S (π i) K' ∧
        ∀ w ∈ S, IsCompU (π i) w (σ i w) ∧ fixed (σ i w).ρ (K' w) ≠ ⊥ ∧
          ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed (σ i w).ρ U)) ∧
      (∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → HasLevel S π₀ K' →
        ∃ i, ∀ w ∈ S, IsCompU π₀ w (σ i w)) ∧
      ∀ f, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
        ∑ i, ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = geomU S lam f

def absHalf (w : Pl E) (x : w.adicCompletion E) : ℂ := (Real.sqrt ((qV E w : ℝ) ^ (-ordL x)) : ℝ)

def delta (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (Q₁ Q₂ : (w.adicCompletion E)[X]) : ℂ :=
  let d := ((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree * ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree
  if IsSplitAt w then
    (if h : (-1) ^ (Q₁.natDegree * Q₂.natDegree) * d ≠ 0 then (μ (Units.mk0 _ h) : ℂ) else 0) *
      absHalf w (resultant Q₁ Q₂ ^ 2 / d)
  else (-1) ^ ordL (resultant Q₁ Q₂) * absHalf w (resultant Q₁ Q₂)

def IsCsr (w : Pl E) (Q : (w.adicCompletion E)[X]) : Prop :=
  IsSplitAt w ∨ C (cj w (Q.coeff 0)) * Q = (Q.map (cj w)).reverse

def Match (n a b : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (φ : GLw a w × GLw b w → ℂ) : Prop :=
  ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b →
    (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → stTw2 a b w Q₁ Q₂ φ = delta w μ Q₁ Q₂ * kapOrb n w Q₁ Q₂ f

def HasTransfer (n : ℕ) (w : Pl E) : Prop :=
  ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → ∃ K' ≤ U, IsLevel (MonoidHom.id _) (KL n w) K' ∧
    ∀ a b, a + b = n → ∃ K₁ K₂ φ, IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) K₂ ∧
      IsHecke (K₁.prod K₂) φ ∧ Match n a b w 1 ((K' : Set (UL n w)).indicator 1) φ

def HasBC (π : Submodule ℂ (UA E n → ℂ)) : Prop :=
  ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)) (m : Fin c → (E →+* ℂ) → Multiset ℂ), UnitaryBC.IsBaseChange π h V σ m

def BCCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ w, ¬ IsSplitAt w → IsUnramU π w ∨ HasTransfer n w) → HasBC π

def TransferInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w → HasTransfer n w

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

structure PLat (O : Type) [Ring O] (bar : O → O) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module O La]
  fin : Module.Finite ℤ La
  free : Module.Free ℤ La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0
  adj : ∀ (a : O) x y, EF (a • x) y = EF x (bar a • y)

attribute [instance] PLat.acg PLat.mod PLat.fin PLat.free

variable {O : Type} [Ring O] {bar : O → O}

def IsPeriod (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) ∧ Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y

def IsHolPeriods (D : PLat O bar) {g m : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : Prop :=
  (∀ b ∈ B, IsPeriod D ρ (P b)) ∧ ∀ x, DifferentiableOn ℂ (fun b => P b x) B

def PerCoord (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (d : ℕ) : Prop :=
  ∀ P₀, IsPeriod D ρ P₀ → ∃ (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)))
    (Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ)) (s : Finset D.La) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ IsHolPeriods D ρ B Q ∧
    Z P₀ ∈ B ∧ Q (Z P₀) = P₀ ∧ (∀ b ∈ B, (∀ x ∈ s, ‖Q b x - P₀ x‖ < ε) → Z (Q b) = b) ∧
    (∀ P, IsPeriod D ρ P → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → Z P ∈ B ∧
      ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = h (Q (Z P) x)) ∧
    (∀ P P', IsPeriod D ρ P → IsPeriod D ρ P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) →
      ∀ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, P' x = h (P x)) → Z P' = Z P) ∧
    ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B' → IsHolPeriods D ρ B' P →
      (∀ b ∈ B', ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P b)) B'

def IsIsom (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) : Prop := ∀ x y, D'.EF (w x) (w y) = D.EF x y

def IsMarkedIsom {Λ : Type} (N : ℕ) (D D' : PLat O bar) (t : Λ → D.La) (t' : Λ → D'.La) (w : D.La ≃ₗ[O] D'.La) : Prop :=
  IsIsom D D' w ∧ ∀ a, ∃ e, w (t a) = t' a + N • e

def Genus (p N : ℕ) (D D' : PLat O bar) (t : D.La → D'.La) : Prop :=
  ∃ (f : ℕ → D.La →+ D'.La) (ν : ℕ → ℤ), t = f N ∧
    (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧ ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧ (∀ (c : O) a, ∃ e, f n (c • a) = c • f n a + n • e) ∧
      (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧
      (∀ a', ∃ a e, a' = f n a + n • e) ∧ ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a'

structure Fam (R : Type) [CommRing R] (O : Type) [Ring O] (Λ : Type) (g : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  A : Over X
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  act_one : act 1 = 𝟙 A
  act_mul : ∀ a b, act (a * b) = act b ≫ act a
  act_add : ∀ a b, act (a + b) = act a * act b
  L : LB A.left
  isLB : L.IsLB
  ample : Out.RelAmple A L
  eta : Λ → (𝟙_ (Over X) ⟶ A)

attribute [instance] Fam.grp Fam.comm

variable {R : Type} [CommRing R] {Λ : Type} {g : ℕ}

def IsExp {X : Scheme.{0}} {G : Over X} [GrpObj G] (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left

def UnifAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La)
    (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) : Prop :=
  y ≫ F.s = spMap σ ∧ IsPeriod D' ρ P ∧ IsExp y e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧
    (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ F.act a) ∧
    (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs F.A F.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) ∧
    ∀ a, toUnit _ ≫ F.eta a = e ((N : ℂ)⁻¹ • P (t a))

structure FineAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) : Prop where
  pts : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ D' t P e, C D' t ∧ UnifAt F σ ρ N D' t P y e
  occ : ∀ D' t P, C D' t → IsPeriod D' ρ P → ∃ y e, UnifAt F σ ρ N D' t P y e
  sep : ∀ (D' D'' : PLat O bar) t t' P P' y y' e e', UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y' e' →
    ∀ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w →
      (∀ x, P' (w x) = h (P x)) → y = y'

structure Unif (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) where
  n : ℕ
  Di : Fin n → PLat O bar
  t : ∀ i, Λ → (Di i).La
  mem : ∀ i, C (Di i) (t i)
  ne : ∀ i, ∃ P, IsPeriod (Di i) ρ P
  all : ∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w
  distinct : ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j
  u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ F.X)
  ex : ∀ i P, (Fin g → ℂ) → (Over.mk (u i P) ⟶ F.A)
  unif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F σ ρ N (Di i) (t i) P (u i P) (ex i P)
  onto : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ i P, IsPeriod (Di i) ρ P ∧ u i P = y
  disj : ∀ i j P P', IsPeriod (Di i) ρ P → IsPeriod (Di j) ρ P' → u i P = u j P' → i = j
  fibre : ∀ i P P', IsPeriod (Di i) ρ P → IsPeriod (Di i) ρ P' → (u i P = u i P' ↔
    ∃ (w : (Di i).La ≃ₗ[O] (Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (Di i) (Di i) (t i) (t i) w ∧ ∀ x, P' (w x) = h (P x))
  hol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))), IsOpen B →
    IsHolPeriods (Di i) ρ B P → IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left)
  lift : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
    (∀ b ∈ B, y b ≫ F.s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B,
    ∃ (B' : Set (Fin m → ℂ)) (i : Fin n) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (Di i) ρ B' P ∧ ∀ b ∈ B', u i (P b) = y b

def FullMark (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) : Prop := ∀ x, ∃ a e, x = t a + N • e

def IsBC (F' : Fam ℂ O Λ g) (F : Fam R O Λ g) (σ : R →+* ℂ) : Prop :=
  ∃ (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsPullback f F'.s F.s (spMap σ) ∧ IsGrpPullback F'.A F.A f φ ∧
    (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) ∧ LBIso F'.L (F.L.pull φ) ∧
    ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left

section Groups

variable (D : PLat O bar) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.La) (K : Type) [CommRing K]

def actM (a : O) : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ((b.repr (a • b j) i : ℤ) : K)

end Groups

end GlobalTheory.PELU
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

def IsGal {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} (π : W ⟶ Z) (hπ : π ≫ s = sW) (G : Type) [Group G]
    (act : G → (W ⟶ W)) : Prop :=
  GlobalTheory.ZM.IsGaloisCover G (fun g => act g⁻¹) π

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

theorem mk' (hG : Finite G) (hfin : IsFinite π) (het : Etale π) (hon : Surjective π) (hinv : ∀ g, act g ≫ π = π)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) (hone : act 1 = 𝟙 W)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W), a ≫ π = b ≫ π → ∃! g : G, b = a ≫ act g) :
    IsGal π hπ G act := by
  refine GlobalTheory.ZM.IsGaloisCover.mk hG ?_ ?_ (fun a => hinv a⁻¹) hfin het hon ?_
  · simpa only [inv_one] using hone
  · intro a c
    simpa only [mul_inv_rev] using hmul c⁻¹ a⁻¹
  · intro K _ _ y y' e
    obtain ⟨g, hg, hu⟩ := hfib K y y' e
    refine ⟨g⁻¹, by simpa only [inv_inv] using hg.symm, fun a ha => ?_⟩
    simpa only [inv_inv] using congrArg Inv.inv (hu a⁻¹ ha.symm)

theorem finite (h : IsGal π hπ G act) : Finite G := GlobalTheory.ZM.IsGaloisCover.finite h
theorem etale (h : IsGal π hπ G act) : Etale π := GlobalTheory.ZM.IsGaloisCover.etale h
theorem surjective (h : IsGal π hπ G act) : Surjective π := GlobalTheory.ZM.IsGaloisCover.onto h

theorem act_comp (h : IsGal π hπ G act) (g : G) : act g ≫ π = π := by
  simpa using GlobalTheory.ZM.IsGaloisCover.inv h g⁻¹

theorem fibre (h : IsGal π hπ G act) (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W) :
    a ≫ π = b ≫ π ↔ ∃! g : G, b = a ≫ act g := by
  constructor
  · intro e
    obtain ⟨g, hg, hu⟩ := GlobalTheory.ZM.IsGaloisCover.fibre h K a b e
    refine ⟨g⁻¹, hg.symm, fun g' hg' => ?_⟩
    have := hu g'⁻¹ (by simpa using hg'.symm)
    simp [← this]
  · rintro ⟨g, hg, -⟩
    rw [hg, Category.assoc, h.act_comp]

end IsGal

end GlobalTheory.W1
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory

namespace GlobalTheory.JSW.WhitModel

open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem mem_NA_iff (u : GA E a) : u ∈ NA (E := E) (a := a) ↔ ∃ X : Pos a → Ad E, u = uGL X := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩
    refine Matrix.ext fun i j => ?_
    rw [coe_uGL, uMat_apply]
    split_ifs with h h'
    · subst h; exact h1 i
    · rfl
    · exact h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))
  · rintro ⟨X, rfl⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [coe_uGL, uMat_apply, if_neg (ne_of_gt h), dite_eq_right (not_lt.2 h.le)]
    · rw [coe_uGL, uMat_apply, if_pos rfl]

theorem superDiag_uGL (X : Pos a → Ad E) : GlobalTheory.Whittaker.superDiag (uGL X) = supSum 0 X := by
  classical
  unfold GlobalTheory.Whittaker.superDiag supSum
  refine (Finset.sum_sigma' _ _ _).trans ?_
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.1]
  · intro p _ q _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩
  · intro p _
    simp only [coe_uGL, uMat_apply]
    rw [if_neg (ne_of_lt p.2), dite_eq_left p.2]

theorem whit_mul {F : GA E a → ℂ} (hc : Continuous F) (hl : AutomorphicForm.IsLeftInvariant F) {u : GA E a}
    (hu : u ∈ NA (E := E) (a := a)) (g : GA E a) : whit F (u * g) = psiN u * whit F g := by
  obtain ⟨X, rfl⟩ := (mem_NA_iff u).1 hu
  rw [psiN, superDiag_uGL]
  exact MultiplicityOne.whittaker_uGL_mul hc hl X g

theorem psiLoc_eq (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    psiLoc w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := by
  classical
  rw [psiLoc, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem loc_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) (w.adicCompletion E)) : finGL E a (locGL E a w g) ∈ supS (E := E) (a := a) S ↔ w ∈ S ∨ g = 1 := by
  have hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g) := fun _ _ => rfl
  constructor
  · intro h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have := h w hw
      rw [hc, pFin_finGL, pLoc_locGL] at this
      exact Or.inr this
  · rintro (h | rfl) v hv
    · rw [hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]
    · simp

variable [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.JSW.WhitModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
noncomputable section

namespace GlobalTheory.KS

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

abbrev pow (A : Over S) (m : ℕ) : Over S := ∏ᶜ fun _ : Fin m => A

abbrev pr (A : Over S) {m : ℕ} (i : Fin m) : pow A m ⟶ A := Pi.π (fun _ : Fin m => A) i

def matEnd {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : pow A m ⟶ pow A m :=
  Pi.lift fun i => (List.ofFn fun j => pr A j ≫ act.act (M i j)).prod

def powMap {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (h : φ ≫ A.hom = A'.hom ≫ f)
    (m : ℕ) : (pow A' m).left ⟶ (pow A m).left :=
  (Pi.lift (fun i => Over.homMk ((pr A' i).left ≫ φ) (by
    rw [Category.assoc, h, ← Category.assoc, Over.w]; rfl)) : Over.mk ((pow A' m).hom ≫ f) ⟶ pow A m).left

variable {B B' : Scheme.{0}}

abbrev ksBC (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : Scheme.{0} := pullback ((pow A m).hom ≫ p) b

def matBC {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (M : Matrix (Fin m) (Fin m) O) :
    ksBC A m p b ⟶ ksBC A m p b :=
  pullback.map _ _ _ _ (matEnd act M).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp)

variable (l : ℕ) [Fact l.Prime] (E : Type) [CommRing E] [Algebra ℚ_[l] E]

abbrev HE (Y : Scheme.{0}) (n : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n 0

def pullE {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : HE l E Y' n →ₗ[E] HE l E Y n :=
  (pullHQ l (sch.map u) n 0).baseChange E

variable {E}

def op {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n : ℤ) : Module.End E (HE l E (ksBC A m p b) n) :=
  ε.sum fun M c => c • pullE l E (matBC act p b M) n


variable (E) in
abbrev HEt (Y : Scheme.{0}) (n t : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n t



end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.LBObs

section Frames

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

def IsBas (V : C → X.Opens) : Prop :=
  (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C, x ∈ V t ∧ V t ≤ U) ∧
    ∀ (t₁ t₂ : C) (x : X) (U : X.Opens), x ∈ U → x ∈ V t₁ → x ∈ V t₂ →
      ∃ t₃ : C, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ V t₃ ∧ V t₃ ≤ U

def IsGenOn (L : LB X) (W : X.Opens) (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) : Prop :=
  ∀ m m' : L.ι, res (inf_le_left : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m) (τ m) =
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m') (L.g m m') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ⊓ L.U m ⊓ L.U m' ≤ W ⊓ L.U m') (τ m')

def IsFrame (L : LB X) (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∃ τ : ∀ (T : C) (m : L.ι), Γ(X, V T ⊓ L.U m)ˣ, (∀ T, IsGenOn L (V T) (τ T)) ∧
    ∀ (T T' : C) (a : T ⟶ T') (m : L.ι), res (inf_le_inf_right (L.U m) (hV a)) (τ T m) =
      res (inf_le_left : V T' ⊓ L.U m ≤ V T') (u T T' a) * τ T' m

def IsCoc (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T)
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''), u T T'' (a ≫ b) = res (hV b) (u T T' a) * u T' T'' b

abbrev opOf (G : C ⥤ AffOp X) (T : C) : X.Opens := (G.obj T).unop.1

theorem opOf_le (G : C ⥤ AffOp X) ⦃T T' : C⦄ (a : T ⟶ T') : opOf G T' ≤ opOf G T := leOfHom (G.map a).unop

end Frames

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

def UCoc (F : C ⥤ CommAlgCat.{0} R₀) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''),
    (u T T'' (a ≫ b) : F.obj T'') = mp F b (u T T' a : F.obj T') * (u T' T'' b : F.obj T'')

def IsObU (L : Pre I π F) (α : Aug I π R₁) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ)
    (c : CatCoh.H2 (ext R₁ F)) : Prop :=
  ∃ (v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ) (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T) (z : Z2 (ext R₁ F)),
    (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ (∀ T, α.IsSig (L.p T) (σ T)) ∧ c = H2.mk _ z ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), α.KerQ (B₀ := F.obj T'') (z.1 T T' T'' a b) ∧
        L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z.1 T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'')

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}

def ObAt (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (G : C ⥤ AffOp X₀) (d : CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))) : Prop :=
  ∃ u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X₀, opOf G T')ˣ,
    IsFrame L (opOf G) (opOf_le G) u ∧ IsObU ((ofSys S).restrict G) α u d

def IsObL (S : Sys I π s₀) (α : Aug I π R₁) (L : LB X₀) (c : CatCoh.H2 (ext R₁ (OAff s₀))) : Prop :=
  ∃ (C' : Type) (_ : Category.{0} C') (_ : Quiver.IsThin C') (G : C' ⥤ AffOp X₀), IsBas (opOf G) ∧
    ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)

end GlobalTheory.LBObs
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
noncomputable section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.ObjModel
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1

theorem hatO_integral {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (y v) ≤ 1 := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  have : y ∈ {y : Af E | y v ∈ v.adicCompletionIntegers E} := by
    refine closure_minimal ?_ hc hy
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
    have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
      rw [map_add (f := _)]; rfl
    rw [this]
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)
  exact this

theorem modF_unit {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have h1 : Valued.v ((u : Af E) v) ≤ 1 := hatO_integral hu.1 v
  have h2 : Valued.v ((↑u⁻¹ : Af E) v) ≤ 1 := hatO_integral hu.2 v
  have h3 : Valued.v ((u : Af E) v) * Valued.v ((↑u⁻¹ : Af E) v) = 1 := by
    rw [← map_mul]
    have : (u : Af E) v * (↑u⁻¹ : Af E) v = 1 := (coord v u).val_inv
    rw [this, map_one]
  have h4 : Valued.v ((u : Af E) v) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((u : Af E) v) * 1 := by gcongr
      _ = _ := mul_one _
  simp [h4]

variable {I : Type}

theorem prod_normSq [Fintype I] [_root_.NumberField.IsTotallyComplex E] {φ : I → E →+* ℂ}
    (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  push_cast at h1
  rw [← h1]
  refine Fintype.prod_bijective (fun i => InfinitePlace.mk (φ i)) ⟨fun i j hij => ?_, fun w => ?_⟩ _ _ fun i => ?_
  · obtain ⟨l, -, hl⟩ := h (φ i)
    have h2 := InfinitePlace.mk_eq_iff.1 hij.symm
    rw [hl i (Or.inl rfl), hl j (h2.imp Eq.symm Eq.symm)]
  · obtain ⟨l, hl, -⟩ := h w.embedding
    refine ⟨l, ?_⟩
    rw [← w.mk_embedding]
    exact InfinitePlace.mk_eq_iff.2 (hl.imp Eq.symm Eq.symm)
  · rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]

theorem prod_cpow (t : Finset I) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (z : ℂ) :
    ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ z = ((∏ i ∈ t, r i : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i)]

end GlobalTheory.CMVal.ObjModel
end
end
