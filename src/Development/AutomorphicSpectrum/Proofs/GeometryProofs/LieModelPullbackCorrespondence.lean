module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieMove

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {R : Type} [CommRing R] {x : Sp R ⟶ S'}

theorem fst_comp_alg : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem epsMul_comp_alg (c : R) : Spec.map (CommRingCat.ofHom (epsMul c)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]

def pushEps (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : epsAt (x ≫ f) ⟶ G :=
  Over.homMk (p.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w p]
    exact Category.assoc _ _ _)

def liftEps (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : epsAt x ⟶ G' :=
  Over.homMk (h.1.lift v.left (epsAt x).hom ((Over.w v).trans (Category.assoc _ _ _).symm)) (h.1.lift_snd _ _ _)

theorem pushEps_left (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : (pushEps h p).left = p.left ≫ φ := rfl

theorem liftEps_left (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : (liftEps h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem push_lift (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : pushEps h (liftEps h v) = v :=
  Over.OverMorphism.ext (liftEps_left h v)

theorem pushEps_inj (h : IsGrpPullback G' G f φ) : Function.Injective (pushEps (x := x) h) := fun p q e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w p).trans (Over.w q).symm))

theorem pushEps_mul (h : IsGrpPullback G' G f φ) (p q : epsAt x ⟶ G') :
    pushEps h (p * q) = pushEps h p * pushEps h q := by
  let U : epsAt (x ≫ f) ⟶ Over.mk ((epsAt x).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let V : Over.mk ((epsAt x).hom ≫ f) ⟶ epsAt (x ≫ f) := Over.homMk (𝟙 _) (by simp)
  have UV : U ≫ V = 𝟙 _ := Over.OverMorphism.ext (by simp [U, V])
  have e := h.2 (epsAt x) p q (V ≫ pushEps h p) (V ≫ pushEps h q) (by simp [V, pushEps_left])
    (by simp [V, pushEps_left])
  have e' : U ≫ ((V ≫ pushEps h p) * (V ≫ pushEps h q)) = pushEps h p * pushEps h q := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, UV, Category.id_comp, Category.id_comp]
  rw [← e']
  apply Over.OverMorphism.ext
  rw [pushEps_left, ← e]
  simp [U]

theorem one_left (h : IsGrpPullback G' G f φ) :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))

theorem tan_iff (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') :
    IsTanAt G' x p ↔ IsTanAt G (x ≫ f) (pushEps h p) := by
  constructor
  · intro t
    show _ ≫ p.left ≫ φ = _
    rw [← Category.assoc, t, one_left h]
  · intro t
    refine h.1.hom_ext ?_ ?_
    · rw [Category.assoc, one_left h]
      exact t
    · have w := Over.w p
      have w₁ := Over.w (1 : Over.mk x ⟶ G')
      rw [Category.assoc, w, w₁]
      show _ ≫ Spec.map _ ≫ x = x
      rw [← Category.assoc, fst_comp_alg, Category.id_comp]

def pullModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G (x ≫ f) L) :
    LieModel G' x L where
  pt e := liftEps h (M.pt e)
  tan e := (tan_iff h _).2 (by rw [push_lift]; exact M.tan e)
  inj a b e := M.inj ((push_lift h _).symm.trans ((congrArg (pushEps h) e).trans (push_lift h _)))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((tan_iff h v).1 t)
    exact ⟨e, pushEps_inj h (by rw [push_lift, he])⟩
  add a b := pushEps_inj h (by rw [pushEps_mul, push_lift, push_lift, push_lift, M.add])
  smul c e := by
    refine h.1.hom_ext ?_ ?_
    · rw [liftEps_left, Category.assoc, liftEps_left, M.smul]
    · have w := fun v => Over.w (liftEps (x := x) h v)
      rw [Category.assoc, w, w]
      show Spec.map _ ≫ x = _ ≫ Spec.map _ ≫ x
      rw [← Category.assoc, epsMul_comp_alg]

def pushModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G' x L) :
    LieModel G (x ≫ f) L where
  pt e := pushEps h (M.pt e)
  tan e := (tan_iff h _).1 (M.tan e)
  inj a b e := M.inj (pushEps_inj h e)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (liftEps h v) ((tan_iff h _).2 (by rw [push_lift]; exact t))
    exact ⟨e, by rw [he, push_lift]⟩
  add a b := by rw [M.add, pushEps_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem models_correspond (h : IsGrpPullback G' G f φ) (L : Type) [AddCommGroup L] [Module R L] :
    (∀ M : LieModel G (x ≫ f) L, ∃ M' : LieModel G' x L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧
      ∀ M' : LieModel G' x L, ∃ M : LieModel G (x ≫ f) L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left :=
  ⟨fun M => ⟨pullModel h M, fun _ => liftEps_left h _⟩, fun M' => ⟨pushModel h M', fun _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieMove

theorem GlobalTheory.CompanionTheory.Ar.LieMove.main : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G]
    (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L],
    IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
      ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  intro R _ X x G _ G₀ _ ψ L _ _ h
  have key : ∀ y : Sp R ⟶ X, 𝟙 _ ≫ x = y →
      (∀ M : LieModel G y L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
        ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G y L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
    rintro _ rfl
    exact GlobalTheory.CompanionTheory.Ar.LieMove.models_correspond h L
  exact key x (Category.id_comp x)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_correspondence : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L], IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧ ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieMove.main | exact GlobalTheory.CompanionTheory.Ar.LieMove.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieMove.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

abbrev OCp (p : Nat.Primes) : Type :=
  (NormedField.valuation (K := ℂ_[p])).valuationSubring

def inE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def stdLat (A C : Type) [CommRing A] [Field C] [Algebra A C] (g : ℕ) : Submodule A (Fin g → C) where
  carrier := {x | ∀ i, x i ∈ (algebraMap A C).range}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun a x hx i => by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ (hx i)

section Eval

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {g : ℕ}

def comb {R : Subring Ω} (ℓ : Fin g → Vs) (x : Fin g → R) : Vs := ∑ i, (x i : Ω) • ℓ i

def Tied {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρ : 𝓞 E →+* Module.End Ω Vs)
    (ρC : 𝓞 E →+* Module.End C (Fin g → C)) : Prop :=
  ∀ (a : 𝓞 E) (x x' : Fin g → R), ρ a (comb ℓ x) = comb ℓ x' → ρC a (fun i => ψ (x i)) = fun i => ψ (x' i)

def HodgeAt {R : Subring Ω} {N : ℕ} (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (HL : Submodule R (Vs × Module.Dual Ω Vs)) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs) : Prop :=
  HT.IsFreeOn ρH HL t ∧
    HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ) ∧
    ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R

def IsEval {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C)) : Prop :=
  (∀ (a : 𝓞 E) (h : HL) (h' : ρH a (h : Vs × Module.Dual Ω Vs) ∈ HL), ev ⟨_, h'⟩ = ρHC a (ev h)) ∧
  (∀ (h : HL) (x : Fin g → R), (h : Vs × Module.Dual Ω Vs).1 = comb ℓ x → (ev h).1 = fun i => ψ (x i)) ∧
  (∀ (h : HL) (x : Fin g → R) (r : R), (h : Vs × Module.Dual Ω Vs).1 = 0 →
    (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r)

end Eval
end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure AbQuot (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) where

  tB : SAB H (Sp k)
  proper : IsProper tB.G.hom
  ktriv : Out.KTriv tB.G tB.PP.L

  Ch : Type
  [acg : AddCommGroup Ch]
  [free : Module.Free ℤ Ch]
  [fin : Module.Finite ℤ Ch]

  q : (Over.pullback x).obj t.G ⟶ tB.G
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  i : splitTorus (Sp k) Ch ⟶ (Over.pullback x).obj t.G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ tB.G)

  act_q : ∀ a, (Over.pullback x).map (t.act.act a) ≫ q = q ≫ tB.act.act a

  bun : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (tB.PP.L.pull q.left)

attribute [instance] AbQuot.acg AbQuot.free AbQuot.fin

variable [StarRing (𝓞 E)]

def AbQuot.IsDiff {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} (Q : AbQuot t x) {d d' : ℕ} (g : GermAt t x d)
    (gB : GermAt Q.tB (𝟙 (Sp k)) d') (P : Matrix (Fin d') (Fin d) k) : Prop :=
  ∀ (l : Fin d) (v : Sp (DualNumber k) ⟶ ((Over.pullback x).obj t.G).left),
    v ≫ pullback.fst t.G.hom x = g.tg l → v ≫ ((Over.pullback x).obj t.G).hom = spMap (algebraMap k (DualNumber k)) →
      IsCombAtG Q.tB (𝟙 (Sp k)) gB.tg (fun i => P i l) (v ≫ Q.q.left)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

section Map

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def vmap (f : R →+* S) (y : (Fin d → R) × (Fin d → R)) : (Fin d → S) × (Fin d → S) :=
  (fun i => f (y.1 i), fun i => f (y.2 i))

theorem vmap_add (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y + y') = vmap f y + vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sub (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y - y') = vmap f y - vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_zero (f : R →+* S) : vmap f (0 : (Fin d → R) × (Fin d → R)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_smul (f : R →+* S) (c : R) (y : (Fin d → R) × (Fin d → R)) :
    vmap f (c • y) = f c • vmap f y := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sum {A : Type} (s : Finset A) (f : R →+* S) (y : A → (Fin d → R) × (Fin d → R)) :
    vmap f (∑ i ∈ s, y i) = ∑ i ∈ s, vmap f (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vmap_zero f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vmap_add, ih]

theorem vmap_comp {T : Type} [CommRing T] (f : R →+* S) (g : S →+* T) (y : (Fin d → R) × (Fin d → R)) :
    vmap g (vmap f y) = vmap (g.comp f) y := rfl

theorem lin_map (f : R →+* S) (φ : Germ.Pt R 1 d) (m : ℕ) :
    lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem bil_map (f : R →+* S) (g : Germ.PS R 2 d) (m n : ℕ) :
    bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mulVec' (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun i => f (M.mulVec v i)) = (M.map f).mulVec fun i => f (v i) :=
  funext fun i => RingHom.map_mulVec _ _ _ _

theorem vmap_transH (f : R →+* S) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d)
    (y : (Fin d → R) × (Fin d → R)) :
    vmap f (transH φ ψ lam y) = transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam) (vmap f y) := by
  rw [transH_apply, transH_apply, lin_map, lin_map, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (lin ψ 1).transpose (y.2 + (bil lam 1 1).transpose.mulVec y.1)
    have h2 := map_mulVec' f (bil lam 1 1).transpose y.1
    change (fun i => f ((lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1) i)) = _
    rw [h1, Matrix.transpose_map]
    congr 1
    change _ = (fun i => f (y.2 i)) + ((bil lam 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← h2]
    funext i
    simp

variable {O : Type} [CommRing O] [StarRing O]

theorem rho_map {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O) :
    rho B₂ a = (rho B a).map f := by
  have : B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) := funext (h.act a)
  rw [rho, this, lin_map]
  rfl

theorem vmap_rhoH {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O)
    (y : (Fin d → R) × (Fin d → R)) : vmap f (rhoH B a y) = rhoH B₂ a (vmap f y) := by
  rw [rhoH_apply, rhoH_apply, rho_map h, rho_map h, h.ad, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (rho B (star a)).transpose y.2
    have h2 := map_mulVec' f (bil (B.ad a) 1 1).transpose y.1
    rw [Matrix.transpose_map] at h1 h2
    change (fun i => f (((rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) i)) = _
    change _ = ((rho B (star a)).map f).transpose.mulVec (fun i => f (y.2 i)) -
      ((bil (B.ad a) 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← Matrix.transpose_map] at *
    rw [← h1, ← h2]
    funext i
    simp

end Map

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

section H

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]

def IsHBasis {R : Type} [CommRing R] {d r : ℕ} (B : Germ.FB R d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)) : Prop :=
  LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def eigW {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (τ : 𝓞 E →+* R) :
    Submodule R ((Fin d → R) × (Fin d → R)) :=
  ⨆ a : 𝓞 E, LinearMap.range (rhoH B a - τ a • LinearMap.id)

theorem vmap_mem_eigW {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {f : R →+* S} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB S d (𝓞 E)} (h : IsMapOf f B B₂) (τ : 𝓞 E →+* R) {y : (Fin d → R) × (Fin d → R)}
    (hy : y ∈ eigW B τ) : vmap f y ∈ eigW B₂ (f.comp τ) := by
  refine Submodule.iSup_induction (motive := fun y => vmap f y ∈ eigW B₂ (f.comp τ)) _ hy ?_ ?_ ?_
  · rintro a _ ⟨w, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨vmap f w, ?_⟩
    simp [vmap_sub, vmap_smul, vmap_rhoH h]
  · simp [vmap_zero]
  · intro y y' h1 h2
    rw [vmap_add]
    exact add_mem h1 h2

theorem eigW_induction {R : Type} [CommRing R] {d : ℕ} {B : Germ.FB R d (𝓞 E)} {τ : 𝓞 E →+* R}
    {P : (Fin d → R) × (Fin d → R) → Prop} {w : (Fin d → R) × (Fin d → R)} (hw : w ∈ eigW B τ)
    (hg : ∀ a y, P (rhoH B a y - τ a • y)) (h0 : P 0) (hadd : ∀ y y', P y → P y' → P (y + y')) : P w := by
  refine Submodule.iSup_induction (motive := P) _ hw ?_ h0 hadd
  rintro a _ ⟨y, rfl⟩
  exact hg a y

theorem exists_sub_mem_eigW {R : Type} [CommRing R] {d r : ℕ} {B : Germ.FB R d (𝓞 E)}
    {x : Fin r → (Fin d → R) × (Fin d → R)} (h : IsHBasis B x) (τ : 𝓞 E →+* R)
    (y : (Fin d → R) × (Fin d → R)) : ∃ m : Fin r → R, y - ∑ l, m l • x l ∈ eigW B τ := by
  have hy : y ∈ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) := h.2 ▸ trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    classical
    refine ⟨Pi.single q.1 (τ (RingOfIntegers.basis E q.2)), ?_⟩
    refine Submodule.mem_iSup_of_mem (RingOfIntegers.basis E q.2) ⟨x q.1, ?_⟩
    simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp⟩
  | add y y' _ _ h1 h2 =>
    obtain ⟨m, hm⟩ := h1
    obtain ⟨m', hm'⟩ := h2
    refine ⟨m + m', ?_⟩
    have := add_mem hm hm'
    convert this using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul c y _ h1 =>
    obtain ⟨m, hm⟩ := h1
    refine ⟨c • m, ?_⟩
    have := (eigW B τ).smul_mem c hm
    convert this using 1
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum, smul_eq_mul, mul_smul]

theorem vmap_rel {R R' K L : Type} [CommRing R] [CommRing R'] [CommRing K] [CommRing L] {d r : ℕ} (v₀ : R →+* K)
    (v : R' →+* L) (j : L →+* K) (c : R' →+* R) (h : j.comp v = v₀.comp c) (φ' ψ' : Germ.Pt R 1 d)
    (lam' : Germ.PS R 2 d) (x' : (Fin d → R') × (Fin d → R')) (m : Fin r → R)
    (x : Fin r → (Fin d → R) × (Fin d → R)) :
    vmap v₀ (transH φ' ψ' lam' (vmap c x') - ∑ l, m l • x l) =
      transH (fun i => MvPowerSeries.map v₀ (φ' i)) (fun i => MvPowerSeries.map v₀ (ψ' i))
        (MvPowerSeries.map v₀ lam') (vmap j (vmap v x')) - ∑ l, v₀ (m l) • vmap v₀ (x l) := by
  rw [vmap_sub, vmap_transH, vmap_comp, vmap_comp, h, vmap_sum]
  simp only [vmap_smul]

end H

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)}

def toVec (Ω : Type) [Field Ω] (d : ℕ) :
    ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  LinearMap.prodMap LinearMap.id (dotProductBilin Ω Ω)

def toH (S : GermSys t ξ M) (p : Cpt ξ) (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))

theorem toH_add (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y + y') = toH S p y + toH S p y' := by
  simp [toH, vmap_add]

theorem toH_sub (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y - y') = toH S p y - toH S p y' := by
  simp [toH, vmap_sub]

theorem toH_zero (S : GermSys t ξ M) (p : Cpt ξ) :
    toH S p (0 : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) = 0 := by
  simp [toH, vmap_zero]

theorem toH_smul (S : GermSys t ξ M) (p : Cpt ξ) (c : X.presheaf.stalk p.1)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (c • y) = genMap ξ p c • toH S p y := by
  simp [toH, vmap_smul]

theorem toH_sum {A : Type} (s : Finset A) (S : GermSys t ξ M) (p : Cpt ξ)
    (y : A → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (∑ i ∈ s, y i) = ∑ i ∈ s, toH S p (y i) := by
  simp [toH, vmap_sum]

theorem toH_spec (S : GermSys t ξ M) (p q : Cpt ξ) (h : q.1 ⤳ p.1) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p y = toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom y)) := by
  have h1 : (genMap ξ q).comp (X.presheaf.stalkSpecializes h).hom = genMap ξ p :=
    RingHom.ext fun s => ProjectiveLinePlaces.genMap_specializes h q.2 p.2 s
  rw [toH, toH, vmap_transH, vmap_comp, h1, he]
  rfl

end Gen

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem fullTorsion_of_dominates : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ n hd hp hf k _ i' g hg
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  have e : (spMap i' ≫ ξ') ≫ f = spMap (i'.comp i) ≫ ξ := by
    rw [Category.assoc, hd', ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : (Over.mk (spMap i' ≫ ξ') ⟶ G') →* (Over.mk ((spMap i' ≫ ξ') ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
  have ha : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (u : Over.mk a ⟶ G), u ^ n = 1 →
      ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
    intro a b h u hu
    subst h
    exact ⟨u, rfl, hu⟩
  obtain ⟨u, hl, hu⟩ := tr e (ρ g) ha
  obtain ⟨x, hx⟩ := hf k (i'.comp i) u hu
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  have hw : (spMap i ≫ x.left) ≫ G.hom = ξ' ≫ f := by
    rw [Category.assoc, hxw, hd']
  have hs : spMap (i'.comp i) = spMap i' ≫ spMap i := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (hp.1.lift (spMap i ≫ x.left) ξ' hw) (hp.1.lift_snd _ _ _), ?_⟩
  apply hp.1.hom_ext
  · have h1 : g.left ≫ φ = spMap (i'.comp i) ≫ x.left := by
      rw [← hx, hl]
      rfl
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [h1, hs, Category.assoc]
  · have h2 : g.left ≫ G'.hom = spMap i' ≫ ξ' := by simpa using Over.w g
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    exact h2

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | exact GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorBC

private theorem mul_left_congr_of_base_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (y₀ z₀ : Over.mk f ⟶ G) (y₁ z₁ : Over.mk f' ⟶ G) (hy : y₁.left = y₀.left) (hz : z₁.left = z₀.left) :
    (y₁ * z₁).left = (y₀ * z₀).left := by
  subst h
  have e1 : y₁ = y₀ := Over.OverMorphism.ext hy
  have e2 : z₁ = z₀ := Over.OverMorphism.ext hz
  rw [e1, e2]

private theorem pow_eq_one_congr_of_left_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (g₀ : Over.mk f ⟶ G) (g₁ : Over.mk f' ⟶ G) (hg : g₁.left = g₀.left) (N : ℕ) :
    g₁ ^ N = 1 ↔ g₀ ^ N = 1 := by
  subst h
  have e : g₁ = g₀ := Over.OverMorphism.ext hg
  rw [e]

theorem isTorsionAlong_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  intro R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB
  have hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ) := hB.cart.w
  have hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')),
      h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x :=
    fun _ => (Category.assoc _ _ _).symm
  have lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G),
      (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro Y y
    rw [Category.assoc, hw, ← Category.assoc, Over.w y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]
  · intro Y y z y₀ z₀ hy hz
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let y' : Y' ⟶ Γ.G := Over.homMk (y.left ≫ F) (lift1 Y y)
    let z' : Y' ⟶ Γ.G := Over.homMk (z.left ≫ F) (lift1 Y z)
    let y₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))
    let z₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))
    have hm := hT.mul Y' y' z' y₁ z₁
      (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy)
      (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)
    have hF := hB.mul Y y z y' z' rfl rfl
    rw [← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]
  · intro Y y z h
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    have e := hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G)
      (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G)
      (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)
    have e2 : y.left ≫ F = z.left ≫ F := congrArg (fun m => m.left) e
    apply Over.OverMorphism.ext
    exact hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)
  · intro Y g
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let g₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))
    rw [← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]
    constructor
    · rintro ⟨y', hy'⟩
      refine ⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩
      show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left
      rw [← Category.assoc, hB.cart.lift_fst]
      exact hy'
    · rintro ⟨y, hy⟩
      refine ⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩
      show (y.left ≫ F) ≫ i = g.left
      rw [Category.assoc]
      exact hy

end GlobalTheory.CompanionTheory.Ar.TorBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | exact GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left :=
  fun _ _ _ _ _ _ t => ⟨GlobalTheory.ObjRebase.sabMapId t, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sab_map_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | exact GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sabMap_id <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  simp only [← Scheme.Hom.comp_apply, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_finite_group_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDivides
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDivides
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDividesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_order_divides : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | exact GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIso
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TorIso

variable {R : Type} [CommRing R] [IsDomain R] {T₁ T₂ : Type} [CommGroup T₁] [CommGroup T₂]
  {Γ₁ : BT.QFGroup R T₁} {Γ₂ : BT.QFGroup R T₂} {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {N : ℕ}
  {i₁ : Γ₁.G.left ⟶ G.left} {i₂ : Γ₂.G.left ⟶ G.left}

theorem exists_hom (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) :
    ∃ ψ : Γ₁.G ⟶ Γ₂.G, ψ.left ≫ i₂ = i₁ := by
  let g : Over.mk (Γ₁.G.hom ≫ x) ⟶ G := Over.homMk i₁ h₁.isOver
  have hg : g ^ N = 1 := (h₁.kernel Γ₁.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨y, hy⟩ := (h₂.kernel Γ₁.G g).1 hg
  exact ⟨y, hy⟩

theorem hom_mul (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) (ψ : Γ₁.G ⟶ Γ₂.G)
    (hψ : ψ.left ≫ i₂ = i₁) {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ Γ₁.G) :
    (y * z) ≫ ψ = (y ≫ ψ) * (z ≫ ψ) := by
  have w : ∀ u : Y ⟶ Γ₁.G, (u.left ≫ i₁) ≫ G.hom = (Over.mk (Y.hom ≫ x)).hom := fun u => by
    have := Over.w u
    simp only [Category.assoc, h₁.isOver, Over.mk_hom]
    rw [← Category.assoc, this]
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (y.left ≫ i₁) (w y)
  let z₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (z.left ≫ i₁) (w z)
  have e₁ := h₁.mul Y y z y₀ z₀ rfl rfl
  have e₂ := h₂.mul Y (y ≫ ψ) (z ≫ ψ) y₀ z₀ (by simp [y₀, hψ]) (by simp [z₀, hψ])
  apply h₂.inj
  rw [Over.comp_left, Category.assoc, hψ, ← e₁, e₂]

theorem exists_pt (ψ : Γ₁.G ⟶ Γ₂.G) (t : T₁) : ∃ t', Γ₁.pt t ≫ ψ = Γ₂.pt t' := by
  obtain ⟨t', ht⟩ := BT.QFGroup.exists_eq_comp_pt R T₂ Γ₂ (FractionRing R) (RingHom.id _)
    ((Γ₁.pt t).left ≫ ψ.left) (by
      rw [Category.assoc, Over.w ψ, Over.w (Γ₁.pt t), RingHom.id_comp]
      rfl)
  refine ⟨t', Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ht]
  have : CommRingCat.ofHom (RingHom.id (FractionRing R)) = 𝟙 _ := rfl
  rw [this, Spec.map_id, Category.id_comp]

theorem pt_injective (Γ : BT.QFGroup R T₁) : Function.Injective Γ.pt := fun a b h => by
  let o : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  exact Γ.pt_inj a b o o (by rw [h])

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (g : Y ⟶ X)
    (s : Γ(X, ⊤)) : BT.valAt (y ≫ g) ⊤ le_top s = BT.valAt y ⊤ le_top (g.appTop s) := by
  unfold BT.valAt
  congr 1

theorem exists_mulEquiv_isHT : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  intro R _ _ T₁ T₂ _ _ Γ₁ Γ₂ S G _ x N i₁ i₂ h₁ h₂
  obtain ⟨ψ, hψ⟩ := exists_hom h₁ h₂
  obtain ⟨ψ', hψ'⟩ := exists_hom h₂ h₁
  have c₁ : ψ ≫ ψ' = 𝟙 _ := h₁.inj _ _ _ (by simp [hψ, hψ'])
  have c₂ : ψ' ≫ ψ = 𝟙 _ := h₂.inj _ _ _ (by simp [hψ, hψ'])
  choose f hf using exists_pt (Γ₁ := Γ₁) (Γ₂ := Γ₂) ψ
  choose f' hf' using exists_pt (Γ₁ := Γ₂) (Γ₂ := Γ₁) ψ'
  have fmul : ∀ a c, f (a * c) = f a * f c := fun a c => pt_injective Γ₂ (by
    rw [← hf, map_mul, map_mul, hom_mul h₁ h₂ ψ hψ, hf, hf])
  let b : T₁ ≃* T₂ :=
    { toFun := f
      invFun := f'
      left_inv := fun t => pt_injective Γ₁ (by rw [← hf', ← hf, Category.assoc, c₁, Category.comp_id])
      right_inv := fun t => pt_injective Γ₂ (by rw [← hf, ← hf', Category.assoc, c₂, Category.comp_id])
      map_mul' := fmul }
  refine ⟨b, ?_⟩
  rintro L _ _ M χ w ⟨s, hs, hv⟩
  refine ⟨ψ'.left.appTop s, fun t => ?_, fun e => ?_⟩
  · have e₁ : (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt (f' t)).left := congrArg (fun z => z.left) (hf' t)
    refine (valAt_comp _ _ s).symm.trans ?_
    rw [e₁]
    exact hs (f' t)
  · obtain ⟨v, v₁, v₂, v₃⟩ := hv e
    have e₁ : ψ.left ≫ ψ'.left = 𝟙 _ := congrArg (fun z => z.left) c₁
    refine ⟨v ≫ ψ.left, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w ψ, v₁]
    · rw [Category.assoc, hψ, v₂]
    · refine (valAt_comp _ _ s).symm.trans ?_
      rw [Category.assoc, e₁, Category.comp_id]
      exact v₃

end GlobalTheory.CompanionTheory.Ar.BT.TorIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_along_unique_up_to_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT | exact GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorIso.exists_mulEquiv_isHT <;> assumption)
end
end
