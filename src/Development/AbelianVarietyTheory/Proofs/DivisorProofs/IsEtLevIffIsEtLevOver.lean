module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.PullPt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S T : Scheme.{0}} {s : S ⟶ Sp R} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s₁}

def ptOver (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : Over.mk (U.hom ≫ t) ⟶ o.A :=
  Over.homMk (g.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w g]
    rfl)

@[simp] theorem ptOver_left (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) :
    (ptOver m g).left = g.left ≫ m.φ := rfl

theorem ptOver_injective (m : ObjMap o₁ o t) {U : Over T} : Function.Injective (ptOver m (U := U)) := by
  intro g h e
  have e' : g.left ≫ m.φ = h.left ≫ m.φ := by
    rw [← ptOver_left m g, ← ptOver_left m h, e]
  ext
  exact m.cart.1.hom_ext e' (by rw [Over.w g, Over.w h])

theorem ptOver_surjective (m : ObjMap o₁ o t) {U : Over T} : Function.Surjective (ptOver m (U := U)) := by
  intro g₀
  refine ⟨Over.homMk (m.cart.1.lift g₀.left U.hom (by rw [Over.w g₀]; rfl)) (m.cart.1.lift_snd _ _ _), ?_⟩
  ext
  simp [ptOver, m.cart.1.lift_fst]

theorem ptOver_mul (m : ObjMap o₁ o t) {U : Over T} (g h : U ⟶ o₁.A) :
    ptOver m (g * h) = ptOver m g * ptOver m h := by
  ext
  exact (m.cart.2 U g h (ptOver m g) (ptOver m h) rfl rfl).symm

theorem ptOver_one (m : ObjMap o₁ o t) {U : Over T} : ptOver m (1 : U ⟶ o₁.A) = 1 := by
  have h := ptOver_mul m (1 : U ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOver_eq_one (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : ptOver m g = 1 ↔ g = 1 := by
  rw [← ptOver_one m]
  exact (ptOver_injective m).eq_iff

theorem ptOver_act (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) (c : D.O) :
    ptOver m (g ≫ o₁.act.act c) = ptOver m g ≫ o.act.act c := by
  ext
  simp [ptOver, m.act]

theorem ptOf_eq (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk (𝟙 T) (by simp) : Over.mk ((𝟙_ (Over T)).hom ≫ t) ⟶ Over.mk t) ≫ ptOf m g = ptOver m g := by
  ext
  simp [ptOf, ptOver]

theorem ptOf_injective (m : ObjMap o₁ o t) : Function.Injective (ptOf m) := by
  intro g h e
  apply ptOver_injective m
  rw [← ptOf_eq, ← ptOf_eq, e]

theorem ptOf_mul (m : ObjMap o₁ o t) (g h : 𝟙_ (Over T) ⟶ o₁.A) :
    ptOf m (g * h) = ptOf m g * ptOf m h := by
  have e := ptOf_eq m (g * h)
  rw [ptOver_mul, ← ptOf_eq, ← ptOf_eq, ← comp_mul] at e
  ext
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem ptOf_one (m : ObjMap o₁ o t) : ptOf m (1 : 𝟙_ (Over T) ⟶ o₁.A) = 1 := by
  have h := ptOf_mul m (1 : 𝟙_ (Over T) ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOf_act (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) (c : D.O) :
    ptOf m (g ≫ o₁.act.act c) = ptOf m g ≫ o.act.act c := by
  ext
  simp [ptOf, m.act]

theorem homMk_ptOf (m : ObjMap o₁ o t) {k : Type} [Field k] (x : Sp k ⟶ T) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m g =
      ptOver m (toUnit (Over.mk x) ≫ g) := by
  ext
  simp [ptOf, ptOver]

end GlobalTheory.UPel.HT.EtLev.PullPt

namespace GlobalTheory.UPel.HT.EtLev

open PullPt

theorem isEtLev_iff_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁)
    (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)),
    IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  intro p _ D R _ b N S T s t s₁ o o₁ m w0 r l
  have hadd : (∀ x y, l (x + y) = l x * l y) ↔ (∀ x y, ptOf m (l (x + y)) = ptOf m (l x) * ptOf m (l y)) := by
    refine forall₂_congr fun x y => ?_
    rw [← ptOf_mul, (ptOf_injective m).eq_iff]
  have hlin : (∀ (c : D.O) x, l (c • x) = l x ≫ o₁.act.act c) ↔
      (∀ (c : D.O) x, ptOf m (l (c • x)) = ptOf m (l x) ≫ o.act.act c) := by
    refine forall₂_congr fun c x => ?_
    rw [← ptOf_act, (ptOf_injective m).eq_iff]
  have hker : (∀ x ∈ wSub D w0 r, l x = 1) ↔ (∀ x ∈ wSub D w0 r, ptOf m (l x) = 1) := by
    refine forall₂_congr fun x _ => ?_
    rw [← ptOf_one m, (ptOf_injective m).eq_iff]
  have hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T),
      ((∀ y, toUnit (Over.mk x) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk x ⟶ o₁.A, (∀ c ∈ w0 ^ r, g ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, toUnit (Over.mk x) ≫ l y = g) ↔
      ((∀ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk (x ≫ (Over.mk t).hom) ⟶ o.A,
          (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = g) := by
    intro k _ _ x
    simp only [homMk_ptOf]
    refine and_congr (forall_congr' fun y => by rw [ptOver_eq_one]) ?_
    constructor
    · intro h g₀ hg₀
      obtain ⟨g, rfl⟩ := ptOver_surjective m (U := Over.mk x) g₀
      obtain ⟨y, hy⟩ := h g (fun c hc => by rw [← ptOver_eq_one m, ptOver_act]; exact hg₀ c hc)
      exact ⟨y, by rw [hy]⟩
    · intro h g hg
      obtain ⟨y, hy⟩ := h (ptOver m g) (fun c hc => by rw [← ptOver_act, ptOver_eq_one]; exact hg c hc)
      exact ⟨y, ptOver_injective m hy⟩
  unfold IsEtLev IsEtLevOver
  rw [hadd, hlin, hker]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun x => hgeom k x)))

end GlobalTheory.UPel.HT.EtLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfComp
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DPLoc

variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
  [IsLocalization M S] {J : Ideal B} (δ : DividedPowers J)


include M in
theorem wellDef {u v : S} {j j' : B} (hj : j ∈ J) (hj' : j' ∈ J)
    (h : u * algebraMap B S j = v * algebraMap B S j') (n : ℕ) :
    u ^ n * algebraMap B S (δ.dpow n j) = v ^ n * algebraMap B S (δ.dpow n j') := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M u
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj M v
  simp only at ha hc
  have h1 : algebraMap B S (a * t * j) = algebraMap B S (c * s * j') := by
    simp only [map_mul, ← ha, ← hc]
    linear_combination (algebraMap B S s * algebraMap B S t) * h
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : ((m : B) * (a * t)) ^ n * δ.dpow n j = ((m : B) * (c * s)) ^ n * δ.dpow n j' := by
    rw [← δ.dpow_mul hj, ← δ.dpow_mul hj']
    congr 1
    linear_combination hm
  have h3 := congrArg (algebraMap B S) h2
  simp only [map_mul, map_pow, ← ha, ← hc, mul_pow] at h3
  have hu : IsUnit ((algebraMap B S m) ^ n * (algebraMap B S s) ^ n * (algebraMap B S t) ^ n) :=
    (((IsLocalization.map_units S m).pow n).mul ((IsLocalization.map_units S s).pow n)).mul
      ((IsLocalization.map_units S t).pow n)
  apply hu.mul_left_cancel
  linear_combination h3


include M in
theorem rep₂ {x y : S} (hx : x ∈ J.map (algebraMap B S)) (hy : y ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j j' : B), j ∈ J ∧ j' ∈ J ∧ x = u * algebraMap B S j ∧
      y = u * algebraMap B S j' := by
  obtain ⟨⟨j, s⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  obtain ⟨⟨j', t⟩, hj'⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
  simp only at hj hj'
  obtain ⟨u, hu⟩ := (IsLocalization.map_units S (s * t)).exists_left_inv
  simp only [Submonoid.coe_mul, map_mul] at hu
  refine ⟨u, t * j, s * j', J.mul_mem_left _ j.2, J.mul_mem_left _ j'.2, ?_, ?_⟩
  · rw [map_mul, ← hj]; linear_combination (-x) * hu
  · rw [map_mul, ← hj']; linear_combination (-y) * hu


include M in
theorem rep {x : S} (hx : x ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j : B), j ∈ J ∧ x = u * algebraMap B S j := by
  obtain ⟨u, j, _, hj, _, e, _⟩ := rep₂ M hx hx
  exact ⟨u, j, hj, e⟩


open Classical in
def ext (n : ℕ) (x : S) : S :=
  if h : ∃ p : S × B, p.2 ∈ J ∧ x = p.1 * algebraMap B S p.2 then
    h.choose.1 ^ n * algebraMap B S (δ.dpow n h.choose.2) else 0


include M in
theorem ext_eq (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    ext δ n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) := by
  have h : ∃ p : S × B, p.2 ∈ J ∧ u * algebraMap B S j = p.1 * algebraMap B S p.2 :=
    ⟨(u, j), hj, rfl⟩
  rw [ext, dite_eq_left h]
  exact (wellDef M δ hj h.choose_spec.1 h.choose_spec.2 n).symm

def dp : DividedPowers (J.map (algebraMap B S)) where
  dpow := ext δ
  dpow_null {n x} hx := by
    rw [ext, dite_eq_right]
    rintro ⟨p, hp, rfl⟩
    exact hx (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hp))
  dpow_zero hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_zero hj]
  dpow_one hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_one hj]
  dpow_mem hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (δ.dpow_mem hn hj))
  dpow_add hx hy := by
    obtain ⟨u, j, j', hj, hj', rfl, rfl⟩ := rep₂ M hx hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← mul_add, ← map_add (f := _), ext_eq M δ _ _ (J.add_mem hj hj'), δ.dpow_add hj hj', map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj', ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hk : k.1 + k.2 = _), map_mul]
    ring
  dpow_mul hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [← mul_assoc, ext_eq M δ _ _ hj, ext_eq M δ _ _ hj]
    ring
  mul_dpow {m n x} hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    have := congrArg (algebraMap B S) (δ.mul_dpow (m := m) (n := n) hj)
    rw [map_mul, map_mul, map_natCast] at this
    simp only [ext_eq M δ _ _ hj]
    linear_combination u ^ (m + n) * this
  dpow_comp {m n x} hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj, ext_eq M δ _ _ (δ.dpow_mem hn hj),
      δ.dpow_comp hn hj, map_mul, map_natCast]
    ring

theorem dp_dpow (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    (dp M δ).dpow n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) :=
  ext_eq M δ n u hj

theorem isDPMorphism : IsDPMorphism δ (dp (S := S) M δ) (algebraMap B S) :=
  ⟨le_rfl, fun {n} a ha ↦ by simpa using dp_dpow M δ n (1 : S) ha⟩

theorem isNilDP (h : IsNilDP δ) : IsNilDP (dp (S := S) M δ) := by
  obtain ⟨N, h⟩ := h
  have key : ∀ l : List (ℕ × S), (∀ p ∈ l, p.2 ∈ J.map (algebraMap B S)) →
      ∃ (c : S) (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) ∧
        (l'.map Prod.fst).sum = (l.map Prod.fst).sum ∧
        (l.map fun p ↦ (dp M δ).dpow p.1 p.2).prod =
          c * algebraMap B S (l'.map fun p ↦ δ.dpow p.1 p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ ↦ ⟨1, [], by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨c, l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      obtain ⟨u, j, hj, e⟩ := rep M (hl p (by simp))
      refine ⟨u ^ p.1 * c, (p.1, j) :: l', ?_, by simp [h2], ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        exacts [hj, h1 q hq]
      · simp only [List.map_cons, List.prod_cons, map_mul]
        rw [h3, e, dp_dpow M δ _ _ hj]
        ring
  refine ⟨N, fun l hl hN ↦ ?_⟩
  obtain ⟨c, l', h1, h2, h3⟩ := key l hl
  rw [h3, h l' h1 (h2 ▸ hN), map_zero, mul_zero]

theorem isDPMorphism_of_comp {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'')
    (g : S →+* C) (h : IsDPMorphism δ δ'' (g.comp (algebraMap B S))) :
    IsDPMorphism (dp M δ) δ'' g := by
  refine ⟨by rw [Ideal.map_map]; exact h.1, fun {n} x hx ↦ ?_⟩
  obtain ⟨u, j, hj, rfl⟩ := rep M hx
  have hm : g (algebraMap B S j) ∈ J'' := h.1 (Ideal.mem_map_of_mem _ hj)
  have e : δ''.dpow n (g (algebraMap B S j)) = g (algebraMap B S (δ.dpow n j)) := h.2 j hj
  rw [dp_dpow M δ _ _ hj, map_mul, δ''.dpow_mul hm, e, map_mul, map_pow]

theorem exists_away : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (b : B), IsNilDP δ → ∃ δ' : DividedPowers (J.map (algebraMap B (Localization.Away b))), IsNilDP δ' ∧ IsDPMorphism δ δ' (algebraMap B (Localization.Away b)) ∧ ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : Localization.Away b →+* C), IsDPMorphism δ δ'' (g.comp (algebraMap B _)) → IsDPMorphism δ' δ'' g :=
  fun _ _ _ δ b h ↦ ⟨dp (Submonoid.powers b) δ, isNilDP _ δ h, isDPMorphism _ δ,
    fun _ _ _ δ'' g hg ↦ isDPMorphism_of_comp _ δ δ'' g hg⟩

end GlobalTheory.DPLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledCoisometryNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

def sumGram {K : Type} [Zero K] (N : ℕ) {n : ℕ} (G' : Matrix (Fin n) (Fin n) K) (g : K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b =>
    if ha : a.1 < n then (if hb : b.1 < n then G' ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else (if b.1 < n then 0 else g)

theorem sumGram_entries {K : Type} [Zero K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    (∀ a b : Fin n, sumGram N G' g (iC hN a) (iC hN b) = G' a b) ∧
      (∀ a : Fin n, sumGram N G' g (iC hN a) (iL hN) = 0 ∧ sumGram N G' g (iL hN) (iC hN a) = 0) ∧
      sumGram N G' g (iL hN) (iL hN) = g := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [sumGram, iC, iL]

def nrmSq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (f : VV K lam) : ℝ :=
  (s (pairK lam G f f)).re

def IsScaledCoisometry {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (P : VV K lam →ₗ[K] VV K sg) (κ : ℝ) : Prop :=
  ∃ Q : VV K sg →ₗ[K] VV K lam,
    (∀ (y : VV K sg) (f : VV K lam), pairK lam G (Q y) f = pairK sg G' y (P f)) ∧
    ∀ y y' : VV K sg, s (pairK lam G (Q y) (Q y')) = (κ : ℂ) * s (pairK sg G' y y')

def orthSq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : ℝ :=
  ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (lam τ) (sg τ)

def brSq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (T : ℝ) : ℝ :=
  ∏ τ, T ^ (-nBr (lam τ) (sg τ)) * (((cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (lam τ) (sg τ))

def NormConcl {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (t : ι → K) (T : ℝ) : Prop :=
  0 < brSq hN lam sg T ∧
  IsScaledCoisometry s lam sg G G' (brAt hN lam sg t) (brSq hN lam sg T) ∧
  (∀ f : VV K lam, nrmSq s sg G' (brAt hN lam sg t f) ≤ brSq hN lam sg T * nrmSq s lam G f) ∧
  ∃ f : VV K lam, f ≠ 0 ∧ nrmSq s sg G' (brAt hN lam sg t f) = brSq hN lam sg T * nrmSq s lam G f

def BrNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (s : K →+* ℂ), (∀ x, s (star x) = star (s x)) →
  ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Interlace hN (lam τ) (sg τ)) → (∀ τ, SameShift (lam τ) (sg τ)) →
  ∀ (G' : ι → Matrix (Fin n) (Fin n) K), (∀ τ, ((G' τ).map s).PosDef) →
  ∀ (g t : ι → K) (T : ℝ), 0 < T → (∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ)) →
    NormConcl s hN lam sg (fun τ => sumGram N (G' τ) (g τ)) G' t T

theorem brSq_eq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ}
    (hT : 0 < T) : brSq hN lam sg T = T ^ (-∑ τ, nBr (lam τ) (sg τ)) * orthSq hN lam sg := by
  unfold brSq orthSq
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hT.ne', ih]

def wtOneZero : DomWeight 2 := ⟨![1, 0], by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

def wtZero : DomWeight 1 := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms
end
end

open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.BrNormCompare

open GlobalTheory.IndefiniteRowSideFullHecke

theorem gramSum_eq_sumGram {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    OrthogonalNormSquareSum.gramSum hN G' g = ScaledCoisometryNorms.sumGram N G' g := by
  ext a b
  simp only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]
  by_cases ha : a.1 < n
  · simp [ha]
  · by_cases hb : b.1 < n
    · simp [ha, hb]
    · have h1 : a = Br.iL hN := Fin.ext (by have := a.2; simp only [Br.iL]; omega)
      have h2 : b = Br.iL hN := Fin.ext (by have := b.2; simp only [Br.iL]; omega)
      rw [dite_eq_right ha, dite_eq_right ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]

theorem length_eq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) (hs : ∀ x : K, s (star x) = star (s x)) (g t : K) :
    s (star t * g * t) = ((‖s t‖ ^ 2 : ℝ) : ℂ) * s g := by
  rw [map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

section

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

theorem isScaledCoisometry_iff (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' P ρ ↔ 0 < ρ ^ 2 ∧ ScaledCoisometryNorms.IsScaledCoisometry s lam sg G G' P (ρ ^ 2) := by
  unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry
  refine and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩
  rintro rfl
  simp at h

theorem factor_nonneg (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    0 ≤ OrthogonalNormSquareSum.factor hN lam sg T :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)

theorem prod_factor_sq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ^ 2 = ScaledCoisometryNorms.brSq hN lam sg T := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT

theorem const_eq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg = ScaledCoisometryNorms.brSq hN lam sg T :=
  (ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm

theorem whole_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) {T : ℝ} (hT : 0 < T) :
    (OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' (Br.brAt hN lam sg t) (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ∧
      OrthogonalNormSquareSum.HasOpNormSq s lam G sg G' (Br.brAt hN lam sg t)
        (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg)) ↔
    ScaledCoisometryNorms.NormConcl s hN lam sg G G' t T := by
  rw [isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT),
    prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]
  rfl

theorem single_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin n) (Fin n) K) (t : K) {T : ℝ} (hT : 0 < T) :
    OrthogonalNormSquareSum.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ => G) (fun _ : Unit => sg) (fun _ => G')
        (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t) (OrthogonalNormSquareSum.factor hN lam sg T) ↔
      0 < ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T ∧
        ScaledCoisometryNorms.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => G) (fun _ => G')
          (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t)
          (ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T) := by
  rw [isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]
  simp

end

theorem lastMapNorm_iff_brNorm : OrthogonalNormSquareSum.LastMapNorm ↔ ScaledCoisometryNorms.BrNorm := by
  constructor
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht
    have := (h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2
    rw [whole_iff s hN lam sg _ G' t hT] at this
    simpa only [gramSum_eq_sumGram] using this
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht
    have ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ) := fun τ => by rw [← length_eq s hs, ht τ]
    refine ⟨fun τ => ?_, ?_⟩
    · have := h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ)
        (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)
      rw [single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]
      exact ⟨this.1, this.2.1⟩
    · rw [whole_iff s hN lam sg _ G' t hT]
      simpa only [gramSum_eq_sumGram] using h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'

theorem last_ineq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h1 : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (a : ℝ) (ha : ∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) :
    ∑ τ, (2 * ((N : ℝ) - 1) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      2 * ∑ τ, ((N : ℝ) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) := by
    refine Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)
    have := h1 τ i
    simp only [Br.aBr, Br.bBr] at this
    omega
  have hs : (1 : ℤ) ≤ (lam τ).spread := by
    have hpos : 0 < N := by omega
    have := (lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [DomWeight.spread, dif_pos hpos]
    omega
  have hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) := by exact_mod_cast hd
  have hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ) := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (2 * a) := Real.log_nonneg (hs'.trans (ha τ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  nlinarith [sq_nonneg (N : ℝ)]

end GlobalTheory.BrNormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMul
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CmpB

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (u v : R) :
    (blk d k u v).transpose = blk d k u v := Matrix.diagonal_transpose _

theorem tau_dvd_entry {R : Type} [CommRing R] (t : R) {m n h : Type} [Fintype n]
    (A : Matrix m n R) (Y : Matrix n h R) (hA : ∀ i j, t ∣ A i j) (i : m) (j : h) :
    t ∣ (A * Y) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hA i l) _

theorem comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X Y Z hU' hn1 hn2 hX hX1 hY hZ hZY
  set P := blk d k (p : F.B) 1 with hP

  have hT : P * U'.transpose * X.transpose = (X.map F.σ).transpose * P * U.transpose := by
    have := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_mul, hP, blk_transpose] at this
    simpa only [Matrix.mul_assoc] using this
  have hΔ : (Z - X.transpose * Y).map F.σ = P * U'.transpose * (Z - X.transpose * Y) := by
    have e1 : (X.transpose * Y).map F.σ = P * U'.transpose * (X.transpose * Y) := by
      rw [Matrix.map_mul, Matrix.transpose_map, hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hT, Matrix.mul_assoc (P * U'.transpose)]
    rw [Matrix.map_sub _ (map_sub F.σ), hZ, e1, Matrix.mul_sub]
  have hdiv : ∀ i m, F.τ ∣ (Z - X.transpose * Y) i m := by
    intro i m
    have e : Z - X.transpose * Y = (Z - Y) - (X.transpose - 1) * Y := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    refine dvd_sub (by simpa using hZY i m) (tau_dvd_entry _ _ _ (fun a b => ?_) i m)
    have h1 : (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) a b = (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) b a := by
      simp only [Matrix.one_apply, eq_comm]
    rw [Matrix.sub_apply, Matrix.transpose_apply, h1]
    exact hX1 b a
  have := (GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd p C v O hv ε hε F d k h U' hU' hn1 hn2).1 _ hΔ hdiv
  exact (sub_eq_zero.1 this)

end GlobalTheory.CmpB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMulStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfFrame_solution_congr_eq_transpose_mul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  first | exact @GlobalTheory.CmpB.comparison | exact GlobalTheory.CmpB.comparison | (intros; apply GlobalTheory.CmpB.comparison <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTranspose
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CmpG.comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X u l Gm W hU hN1 hN2 hu hX hXc hl hlc hG hW hWc
  classical
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  obtain ⟨c, hc⟩ := hu
  have hue : u = 1 + F.τ * c := by rw [← hc]; ring
  set w : F.B := 1 - F.τ * c with hwdef
  have hwu : w * u = 1 := by rw [hue, hwdef]; linear_combination (-(c * c)) * F.τ_sq
  have hτ0 : F.θ F.τ = 0 := GlobalTheory.WinLift.theta_tau F hv hε
  have hθu : F.θ u = 1 := by rw [hue, map_add (f := _), map_one, map_mul, hτ0, zero_mul, add_zero]
  have hθw : F.θ w = 1 := by rw [hwdef, map_sub, map_one, map_mul, hτ0, zero_mul, sub_zero]
  have hwU : IsUnit w := ⟨⟨w, u, hwu, by rw [mul_comm]; exact hwu⟩, rfl⟩
  set P := blk d k (p : F.B) 1 with hP
  set D : Matrix (Fin d ⊕ Fin k) (Fin h) F.B := X * W - l • Gm.transpose with hDdef
  have hsm : (l • Gm.transpose).map F.σ = F.σ l • Gm.transpose.map F.σ :=
    Matrix.ext fun i j => by simp
  have hsub : D.map F.σ = (X * W).map F.σ - (l • Gm.transpose).map F.σ :=
    by rw [hDdef]; exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hD : U * P * D.map F.σ = ((p : F.B) * u) • D := by
    rw [hsub, Matrix.map_mul, hsm, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← hX,
      Matrix.mul_assoc, hW, hG, hl, Matrix.mul_smul, smul_smul, hDdef, smul_sub, smul_smul]
    congr 1
    rw [show u * l * (p : F.B) = p * u * l by ring]
  set U₁ := w • U with hU₁
  have hD1 : U₁ * P * D.map F.σ = (p : F.B) • D := by
    rw [hU₁, Matrix.smul_mul, Matrix.smul_mul, hD, smul_smul,
      show w * ((p : F.B) * u) = p by linear_combination (p : F.B) * hwu]
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hU₁u : IsUnit U₁ := by
    rw [Matrix.isUnit_iff_isUnit_det, hU₁, Matrix.det_smul]
    exact (hwU.pow _).mul hUdet
  have hinv : U₁.transpose⁻¹ = u • U.transpose⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hU₁, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hwu, one_smul,
      Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hUdet)]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hN1' : IsNil F.θ F.σ (U₁.transpose⁻¹ * blk d k 1 (p : F.B)) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN1
    rw [hinv, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθu, one_mul]
  have hN2' : IsNil F.θ F.σ (U₁ * P) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN2
    rw [hU₁, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθw, one_mul]
  have key := (GlobalTheory.TauUniq.eq_zero_of_tau_dvd p C v O hv ε hε F d k h U₁ hU₁u hN1' hN2').2
  have hdec : D = (X - 1) * W + (W - Gm.transpose) - (l - 1) • Gm.transpose := by
    rw [hDdef, Matrix.sub_mul, Matrix.one_mul, sub_smul, one_smul]; abel
  have hτD : ∀ i m, F.τ ∣ D i m := by
    intro i m
    rw [hdec, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    refine dvd_sub (dvd_add (Finset.dvd_sum fun j _ => ?_) (hWc i m)) (Dvd.dvd.mul_right hlc _)
    exact Dvd.dvd.mul_right (hXc i j) _
  have hD0 : D = 0 := by
    refine Matrix.ext fun i m => ?_
    have hcol := key (fun i => D i m) (funext fun i => by
      have := congrArg (fun M => M i m) hD1
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this) (fun i => hτD i m)
    exact congrFun hcol i
  exact sub_eq_zero.1 hD0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTransposeStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfFrame_solution_mul_congr_Gm_transpose : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  first | exact @GlobalTheory.CmpG.comparison | exact GlobalTheory.CmpG.comparison | (intros; apply GlobalTheory.CmpG.comparison <;> assumption)
end
end
