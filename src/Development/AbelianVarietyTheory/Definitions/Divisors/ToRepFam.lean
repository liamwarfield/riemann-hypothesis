module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

structure RepFam (b : Base D R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : Obj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)

def Model.toRepFam {b : Base D R} {N : ℕ} (M : Model b N) : RepFam b N := ⟨M.X, M.s, M.univ, M.rep⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

structure GDatum where
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

  splitSome : ∃ (q : ℕ) (_ : Fact q.Prime),
    Nonempty ((O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[q]))
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

attribute [instance] GDatum.fld GDatum.nf GDatum.cm GDatum.rng GDatum.alg GDatum.acg GDatum.modO

def _root_.GlobalTheory.UPel.HT.Datum.toG {p : ℕ} [Fact p.Prime] (D : Datum p) : GDatum where
  F := D.F
  bar := D.bar
  bar_eq := D.bar_eq
  ω := D.ω
  tr := D.tr
  nm := D.nm
  tr_eq := D.tr_eq
  nm_eq := D.nm_eq
  disc_neg := D.disc_neg
  O := D.O
  freeO := D.freeO
  finO := D.finO
  m := D.m
  m_pos := D.m_pos
  rankO := D.rankO
  central := D.central
  star := D.star
  star_star := D.star_star
  star_F := D.star_F
  splitSome := ⟨p, inferInstance, D.splitP⟩
  La := D.La
  freeLa := D.freeLa
  finLa := D.finLa
  n := D.n
  n_pos := D.n_pos
  rankLa := D.rankLa
  EF := D.EF
  alt := D.alt
  nondeg := D.nondeg
  adj := D.adj
  a := D.a
  ρc := D.ρc
  ρc_root := D.ρc_root
  tau := D.tau
  tau_ω := D.tau_ω
  dom := D.dom

structure GBase (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] where
  ρ : R
  ρ_root : ρ ^ 2 - G.tr * ρ + G.nm = 0
  t : Fin G.a → (𝓞 G.F →+* R)
  t_ω : ∀ i, t i G.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤

variable {S : Scheme.{0}}

structure GTateIso (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → G.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : G.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * G.EF x y))

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

def actF {A : Over S} [GrpObj A] (act : OActN G.O A) : OAct (𝓞 G.F) A where
  act c := act.act (algebraMap (𝓞 G.F) G.O c)
  hom c := act.hom _
  one := by rw [map_one]; exact act.one
  mul b c := by rw [← act.mul, ← map_mul, mul_comm]
  add b c := by rw [map_add (f := _)]; exact act.add _ _

structure GObj (b : GBase G R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN G.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  rosati : ∀ c : G.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (G.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 G.F) G.O G.ω) (β b.ρ) v →
      ∃ w : Fin G.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 G.F, IsTanScal act x (algebraMap (𝓞 G.F) G.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (actF act) x (β.comp (b.t i)) G.m
  eta : G.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : G.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : GTateIso G k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] GObj.grp GObj.comm

structure GObjMap {b : GBase G R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : GObj b N s') (o : GObj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

structure GenModel (b : GBase G R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : GObj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : GObj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (GObjMap o univ f)

end GlobalTheory.UPel.HT.Gen
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure Pre (b : Base D R) (s : S ⟶ Sp R) where
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

attribute [instance] Pre.grp Pre.comm

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
noncomputable section

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.CompactB (D : Datum p) : Prop := 2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

variable {R : Type} [CommRing R]

def Lifts {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X) : Prop :=
  z ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) ∧
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = P

def unitPt (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] : Sp B ⟶ A.left :=
  spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left)

def IsSum {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (α : B → B') (f : M → M') : Prop :=
  (∀ b, β (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (α b)) ∧ ∀ m, β (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m)

structure TanRep (A : Over (Sp R)) [GrpObj A] (W : Type) [AddCommGroup W] [Module R W] where

  Φ : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (_ : Sp (TrivSqZeroExt B M) ⟶ A.left), W →ₗ[R] M

  bij : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (l : W →ₗ[R] M),
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ Φ z = l

  nat : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
    [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] (α : B →ₐ[R] B') (f : M →ₗ[R] M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f →
    ∀ z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z → Φ (spMap β ≫ z) = f ∘ₗ Φ z

end GlobalTheory.AbTan

namespace GlobalTheory.AbTan.MultGroup

open LaurentPolynomial

variable (R : Type) [CommRing R]

local instance hopfLaurent : HopfAlgebra (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹]) :=
  inferInstanceAs (HopfAlgebra R R[T;T⁻¹])

abbrev G : Over (Sp R) := (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))

theorem G_hom : (G R).hom = spMap (algebraMap R R[T;T⁻¹]) := rfl

theorem unit_eq (B : Type) [CommRing B] [Algebra R B] :
    unitPt (G R) B = spMap (algebraMap R B) ≫ spMap (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom := rfl

theorem comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem inj' {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B} (h : spMap p = spMap q) : p = q := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

variable {R}

def pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : R[T;T⁻¹] →+* C :=
  (Spec.preimage (R := CommRingCat.of R[T;T⁻¹]) (S := CommRingCat.of C) z).hom

theorem spMap_pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : spMap (pre z) = z := by
  simp only [spMap, pre, CommRingCat.ofHom_hom]
  exact Spec.map_preimage z

theorem pre_spMap {C : Type} [CommRing C] (φ : R[T;T⁻¹] →+* C) : pre (R := R) (spMap φ) = φ := by
  simp only [pre, spMap, Spec.preimage_map, CommRingCat.hom_ofHom]

theorem hom_ext' {C : Type} [CommRing C] {φ ψ : R[T;T⁻¹] →+* C}
    (h0 : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) (h1 : φ (T 1) = ψ (T 1)) : φ = ψ := by
  have hC : ∀ a : R, φ (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a) := fun a => by
    rw [LaurentPolynomial.C_eq_algebraMap]
    exact congrArg (fun f : R →+* C => f a) h0
  have hinv : φ (T (-1)) = ψ (T (-1)) := by
    have e : (T (-1) : R[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; simp
    have eφ : φ (T (-1)) * φ (T 1) = 1 := by rw [← map_mul, e, map_one]
    have eψ : ψ (T 1) * ψ (T (-1)) = 1 := by rw [← map_mul, mul_comm, e, map_one]
    calc φ (T (-1)) = φ (T (-1)) * (ψ (T 1) * ψ (T (-1))) := by rw [eψ, _root_.mul_one]
      _ = (φ (T (-1)) * φ (T 1)) * ψ (T (-1)) := by rw [h1, _root_.mul_assoc]
      _ = ψ (T (-1)) := by rw [eφ, _root_.one_mul]
  have hT : ∀ n : ℤ, φ (T n) = ψ (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [T_add, map_mul, map_mul, ih, h1]
    | pred k ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hinv]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hT]

theorem lifts_iff {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (φ : R[T;T⁻¹] →+* TrivSqZeroExt B M) :
    Lifts (G R).hom (unitPt (G R) B) (spMap φ) ↔
      φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) ∧ (φ (T 1)).fst = 1 := by
  have hε : Bialgebra.counitAlgHom R R[T;T⁻¹] (T 1) = 1 := by
    rw [Bialgebra.counitAlgHom_apply]
    exact AddMonoidAlgebra.counit_single (1 : ℤ) (1 : R)
  have hεC : ∀ r : R, Bialgebra.counitAlgHom R R[T;T⁻¹] (algebraMap R _ r) = r := fun r =>
    (Bialgebra.counitAlgHom R R[T;T⁻¹]).commutes r
  have e1 : spMap φ ≫ (G R).hom = spMap (φ.comp (algebraMap R _)) := by
    rw [G_hom]; exact comp' _ _
  have e2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap φ =
      spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp φ) := comp' _ _
  have e3 : unitPt (G R) B =
      spMap ((algebraMap R B).comp (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom) := by
    rw [unit_eq]; exact comp' _ _
  unfold Lifts
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := inj' (e1.symm.trans h1)
    have h2' := inj' (e2.symm.trans (h2.trans e3))
    refine ⟨h1', ?_⟩
    have := congrArg (fun f : R[T;T⁻¹] →+* B => f (T 1)) h2'
    simpa [hε] using this
  · rintro ⟨h1, h2⟩
    refine ⟨e1.trans (congrArg spMap h1), e2.trans ((congrArg spMap ?_).trans e3.symm)⟩
    apply hom_ext'
    · ext r
      have := congrArg (fun f : R →+* TrivSqZeroExt B M => (f r).fst) h1
      simpa [hεC] using this
    · simpa [hε] using h2

def tanRep : TanRep (G R) R where
  Φ z := LinearMap.toSpanSingleton R _ (pre z (T 1)).snd
  bij := by
    intro B M _ _ _ _ _ _ _ _ l
    let u : (TrivSqZeroExt B M)ˣ :=
      ⟨TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1), TrivSqZeroExt.inl 1 - TrivSqZeroExt.inr (l 1),
        by ext <;> simp, by ext <;> simp⟩
    let φ := LaurentPolynomial.eval₂ ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) u
    have hT : φ (T 1) = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1) := by
      simp [φ, u, LaurentPolynomial.eval₂_T]
    have hC : φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := by
      refine RingHom.ext fun r => ?_
      simp [φ, ← LaurentPolynomial.C_eq_algebraMap]
    refine ⟨spMap φ, ⟨(lifts_iff φ).2 ⟨hC, by simp [hT]⟩, ?_⟩, ?_⟩
    · ext; simp [pre_spMap, hT]
    · rintro z ⟨hz, hl⟩
      rw [← spMap_pre z] at hz ⊢
      obtain ⟨h1, h2⟩ := (lifts_iff _).1 hz
      refine congrArg _ (hom_ext' (h1.trans hC.symm) ?_)
      have h3 : (pre z (T 1)).snd = l 1 := by rw [← hl]; simp
      rw [hT]; ext
      · simp [h2]
      · simp [h3]
  nat := by
    intro B M _ _ _ _ _ _ _ _ B' M' _ _ _ _ _ _ _ _ α f β hβ z _
    have : pre (spMap β ≫ z) = β.comp (pre z) := by
      apply inj'
      rw [spMap_pre, ← comp']
      erw [spMap_pre]
      rfl
    ext
    simp only [this, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply, RingHom.comp_apply]
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (pre z (T 1)), map_add (f := _), hβ.1, hβ.2]
    simp

end GlobalTheory.AbTan.MultGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIntMulIntegral
noncomputable section

open NumberField Matrix Polynomial

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.skewFun (x y : D.La) : Module.Dual ℚ D.F :=
  (integralBasis D.F).constr ℚ fun k =>
    ((D.EF (algebraMap (𝓞 D.F) D.O (RingOfIntegers.basis D.F k) • x) y : ℤ) : ℚ)

theorem Datum.EF_swap (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt, zero_add, add_zero] at h
  linarith

def Datum.Kq : Subfield D.F := (IntermediateField.adjoin ℚ {(D.ω : D.F)}).toSubfield

section Places

variable {F : Type} [Field F] [NumberField F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])

end Places

section Examples

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

end Examples

end GlobalTheory.UPel.HT
end
end
