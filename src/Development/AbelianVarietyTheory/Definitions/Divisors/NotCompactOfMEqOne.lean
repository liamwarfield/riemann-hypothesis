module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

structure Datum (p : ℕ) [Fact p.Prime] where

  F : Type
  [fld : Field F]
  [nf : NumberField F]
  [cm : IsCMField F]

  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)

  ω : 𝓞 F
  tr : ℤ
  nm : ℤ
  tr_eq : ω + bar ω = (tr : 𝓞 F)
  nm_eq : ω * bar ω = (nm : 𝓞 F)
  disc_neg : tr ^ 2 - 4 * nm < 0
  disc_p : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm
  split : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm

  O : Type
  [rng : Ring O]
  [alg : Algebra (𝓞 F) O]
  freeO : Module.Free ℤ O
  finO : Module.Finite ℤ O
  m : ℕ
  m_pos : 0 < m
  rankO : Module.finrank ℤ O = m ^ 2 * Module.finrank ℚ F
  central : ∀ x : O, (∀ y, x * y = y * x) → ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c

  star : O ≃+* Oᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x
  star_F : ∀ c : 𝓞 F, star (algebraMap (𝓞 F) O c) = MulOpposite.op (algebraMap (𝓞 F) O (bar c))

  splitP : Nonempty ((O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[p]))

  La : Type
  [acg : AddCommGroup La]
  [modO : Module O La]
  freeLa : Module.Free ℤ La
  finLa : Module.Finite ℤ La
  n : ℕ
  n_pos : 1 ≤ n
  rankLa : Module.finrank ℤ La = m * n * Module.finrank ℚ F

  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : Function.Injective EF
  perfP : ∃ e : ℕ, e.Coprime p ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f
  adj : ∀ (b : O) x y, EF (b • x) y = EF x ((star b).unop • y)

  a : ℕ
  ρc : ℂ
  ρc_root : ρc ^ 2 - tr * ρc + nm = 0
  tau : Fin a ↪ (F →+* ℂ)
  tau_ω : ∀ i, tau i (ω : F) = ρc

  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    (∀ (b : O) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) → J ∘ₗ A = A ∘ₗ J) ∧
    ∀ (c : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (algebraMap (𝓞 F) O c • x)) →
      let S : ℂ := (m : ℂ) * (∑ i, tau i (c : F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : F →+* ℂ => τ (ω : F) = (starRingEnd ℂ) ρc), (n : ℂ) * τ (c : F) -
        ∑ i, (starRingEnd ℂ) (tau i (c : F)))
      LinearMap.trace ℝ _ A = 2 * S.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * S.im

attribute [instance] Datum.fld Datum.nf Datum.cm Datum.rng Datum.alg Datum.acg Datum.modO

variable {p : ℕ} [Fact p.Prime]

def Datum.IsDivision (D : Datum p) : Prop :=
  ∀ x : D.O, x ≠ 0 → ∃ y : D.O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : D.O)

def Datum.IsSimple (D : Datum p) : Prop := D.a = 1 ∧ D.m = D.n ∧ D.IsDivision

def Datum.Compact (D : Datum p) : Prop :=
  2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)

structure Base (D : Datum p) (R : Type) [CommRing R] where
  unit : ∀ k : ℕ, k.Coprime p → IsUnit (k : R)
  ρ : R
  ρ_root : ρ ^ 2 - D.tr * ρ + D.nm = 0
  t : Fin D.a → (𝓞 D.F →+* R)
  t_ω : ∀ i, t i D.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤
  apart : ∀ i j, i ≠ j → ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k),
    RingHom.ker (β.comp (t i)) ≠ RingHom.ker (β.comp (t j))

variable {S : Scheme.{0}}

structure OActN (O : Type) [Ring O] (G : Over S) [GrpObj G] where
  act : O → (G ⟶ G)
  hom : ∀ b, IsMonHom (act b)
  one : act 1 = 𝟙 G
  mul : ∀ b c, act (b * c) = act c ≫ act b
  add : ∀ b c, act (b + c) = act b * act c

abbrev epsPtR {R' : Type} [CommRing R'] (x : Sp R' ⟶ S) : Over S :=
  Over.mk (spMap (algebraMap R' (DualNumber R')) ≫ x)

def IsTanScal {O : Type} [Ring O] {R' : Type} [CommRing R'] {G : Over S} [GrpObj G] (act : OActN O G)
    (x : Sp R' ⟶ S) (b : O) (c : R') (v : epsPtR x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    (v ≫ act.act b).left = spMap (epsScaleR c) ≫ v.left

variable (D : Datum p) {R : Type} [CommRing R]

def OActN.toF {G : Over S} [GrpObj G] (act : OActN D.O G) : OAct (𝓞 D.F) G where
  act c := act.act (algebraMap (𝓞 D.F) D.O c)
  hom c := act.hom _
  one := by rw [map_one]; exact act.one
  mul b c := by rw [← act.mul, ← map_mul, mul_comm]
  add b c := by rw [map_add (f := _)]; exact act.add _ _

structure TateIsoO (k : Type) [Field k] (Q : Type) [Group Q] (act : D.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : D.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → n.Coprime p → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → n.Coprime p → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → n.Coprime p → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * D.EF x y))

variable {D}

structure Obj (b : Base D R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN D.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A),
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1
  rosati : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
      ∃ w : Fin D.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] Obj.grp Obj.comm

structure ObjMap {b : Base D R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

structure Model (b : Base D R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension (D.a * (D.n - 1)) s
  univ : Obj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}} {O : Type} [Ring O]

def IsRAct (A : Over S) [GrpObj A] (act : O → (A ⟶ A)) : Prop :=
  (∀ a, IsMonHom (act a)) ∧ act 1 = 𝟙 A ∧ (∀ a b, act (a * b) = act a ≫ act b) ∧
    ∀ a b, act (a + b) = act a * act b

def Adj (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) (act : O → (A ⟶ A)) : Prop :=
  ∀ a, LBIso (Q.pull (lift (fst A A ≫ act a) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar a))).left)

structure ActRep (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grp : GrpObj AH]
  φ : AH.left ⟶ A.left
  φ₂ : (AH ⊗ AH).left ⟶ (A ⊗ A).left
  pb : IsGrpPullback AH A π φ
  sq : IsSquare φ φ₂
  act : O → (AH ⟶ AH)
  isAct : IsRAct AH act
  adj : Adj AH (Q.pull φ₂) bar act
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left)
    (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (act' : O → (A' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' →
    IsRAct A' act' → Adj A' (Q.pull φ₂') bar act' →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ ψ : A'.left ⟶ AH.left, IsGrpPullback A' AH h ψ ∧ ψ ≫ φ = φ' ∧
      ∀ a, (act' a).left ≫ ψ = ψ ≫ (act a).left

attribute [instance] ActRep.grp

theorem IsRAct.of_oAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] (i : OAct O A) : IsRAct A i.act :=
  ⟨i.hom, i.one, i.mul, i.add⟩

theorem IsRAct.op_of_ringAct {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A O) :
    IsRAct A (fun a : Oᵐᵒᵖ => ρ.act a.unop) :=
  ⟨fun _ => ρ.hom _, ρ.map_one, fun _ _ => ρ.map_mul _ _, fun _ _ => ρ.map_add _ _⟩

def IsRAct.toOAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)} (h : IsRAct A act) :
    OAct O A :=
  ⟨act, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end GlobalTheory.EndLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}}

structure HomFixRep (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grpA : GrpObj AH]
  BH : Over H
  [grpB : GrpObj BH]
  φA : AH.left ⟶ A.left
  φB : BH.left ⟶ B.left
  pbA : IsGrpPullback AH A π φA
  pbB : IsGrpPullback BH B π φB
  Φ : AH ⟶ BH
  hom : IsMonHom Φ
  iso : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
      IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

attribute [instance] HomFixRep.grpA HomFixRep.grpB

theorem isGrpPullback_id (A : Over S) [GrpObj A] : IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 _) (by simp)
  have h1 : e ≫ x₀ = x := by ext; simp [e, hx]
  have h2 : e ≫ y₀ = y := by ext; simp [e, hy]
  have h3 : e ≫ (x₀ * y₀) = x * y := by rw [MonObj.comp_mul, h1, h2]
  rw [← h3]; simp [e]

def HomFixRep.toTrivial (A : Over S) [GrpObj A] (L : LB A.left) (M : LB (𝟙_ (Over S)).left)
    (h : LBIso (L.pull (𝟙 _)) ((M.pull (𝟙 _)).pull (toUnit A).left)) : HomFixRep A (𝟙_ (Over S)) L M where
  H := S
  π := 𝟙 S
  AH := A
  BH := 𝟙_ (Over S)
  φA := 𝟙 _
  φB := 𝟙 _
  pbA := isGrpPullback_id A
  pbB := isGrpPullback_id _
  Φ := toUnit A
  hom := inferInstance
  iso := h
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB _ _
    refine ⟨t, ⟨by simp, φA', φB', hA, hB, by simp, by simp, ?_⟩, fun h hh => by simpa using hh.1⟩
    have h1 := hA.1.w
    have h2 := hB.1.w
    have h3 := Over.w Φ'
    have h4 := Over.w (toUnit A)
    have h5 : φB' = B'.hom ≫ t := by simpa using h2
    have h6 : (toUnit A).left = A.hom := by simpa using h4
    rw [h5, h6, ← Category.assoc, h3]; exact h1.symm

def trivLB (X : Scheme.{0}) : LB X where
  «ι» := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB :=
  ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    (congrArg₂ (· * ·) (map_one _) (map_one _)).trans ((_root_.mul_one _).trans (map_one _).symm)⟩

end GlobalTheory.EndLoc
end
end
