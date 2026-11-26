module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem le_preimage_top (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    U ≤ p ⁻¹ᵁ ⊤ := by
  intro _ _
  trivial

noncomputable def sectionsAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom

theorem sectionsAlgebraMap_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    sectionsAlgebraMap k p U =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom :=
  rfl

theorem sectionsAlgebraMap_comp_restrict (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsAlgebraMap k p U) =
      sectionsAlgebraMap k p V := by
  have key : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)) ≫
      X.presheaf.map (homOfLE h).op =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V (le_preimage_top k p V) := by
    rw [Category.assoc, Scheme.Hom.appLE_map]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k p V, ← CommRingCat.hom_comp, key]

theorem sectionsAlgebraMap_restrict_apply (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) (a : k) :
    (X.presheaf.map (homOfLE h).op).hom (sectionsAlgebraMap k p U a) =
      sectionsAlgebraMap k p V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_restrict k p h) a

@[reducible] noncomputable def sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (sectionsAlgebraMap k p U).toAlgebra

theorem algebraMap_sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    @algebraMap k Γ(X, U) _ _ (sectionsAlgebra k p U) = sectionsAlgebraMap k p U :=
  rfl

theorem isScalarTower_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (f : Γ(X, U))
    [Algebra k Γ(X, U)] [Algebra k Γ(X, X.basicOpen f)]
    [Algebra Γ(X, U) Γ(X, X.basicOpen f)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hV : algebraMap k Γ(X, X.basicOpen f) = sectionsAlgebraMap k p (X.basicOpen f))
    (hres : algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) :
    IsScalarTower k Γ(X, U) Γ(X, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [hV, hres, hU, sectionsAlgebraMap_restrict_apply]

theorem finiteType_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Algebra.FiniteType k Γ(X, U.1) := by
  have hft : (p.appLE ⊤ U.1 (le_preimage_top k p U.1)).hom.FiniteType := by
    apply Scheme.Hom.finiteType_appLE p (isAffineOpen_top _) U.2
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hsurj : Function.Surjective ⇑(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, DFunLike.congr_fun hcomp y⟩
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ hsurj
  have hst : (sectionsAlgebraMap k p U.1).FiniteType := by
    rw [sectionsAlgebraMap_eq, CommRingCat.hom_comp]
    exact hft.comp hiso
  have hinst : ‹Algebra k Γ(X, U.1)› = (sectionsAlgebraMap k p U.1).toAlgebra :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun h r
  rw [hinst]
  exact hst

theorem isNoetherianRing_sections (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    IsNoetherianRing Γ(X, U.1) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)

theorem finitePresentation_kaehlerDifferential_sections (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (U : X.affineOpens) [Algebra k Γ(X, U.1)]
    (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  have : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U h
  have : Module.Finite Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := inferInstance
  exact Module.finitePresentation_of_finite ..

private theorem derivIdealSheaf_map_ideal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)) =
        @derivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have htower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have hloc : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hfp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have hI : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have key := map_derivIdeal_away (k := k) (S' := Γ(X, X.basicOpen f)) f (I.ideal U)
  exact key.trans (congrArg (@derivIdeal k _ Γ(X, X.basicOpen f) _ algV) hI)

noncomputable def derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    X.IdealSheafData where
  ideal U := @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  map_ideal_basicOpen := by exact derivIdealSheaf_map_ideal_basicOpen k p I

@[simp] theorem derivIdealSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheaf k p I).ideal U = @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) :=
  rfl

theorem le_derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    I ≤ derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens, I.ideal U ≤ (derivIdealSheaf k p I).ideal U := by
    intro U
    exact @le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  exact h

theorem derivIdealSheaf_mono (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    Monotone (derivIdealSheaf k p) := by
  intro I J h
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p I).ideal U ≤ (derivIdealSheaf k p J).ideal U := by
    intro U
    have hU : I.ideal U ≤ J.ideal U := h U
    rw [derivIdealSheaf_ideal, derivIdealSheaf_ideal]
    exact @derivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) _ _ hU
  exact key

theorem derivIdealSheaf_mul_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I J : X.IdealSheafData) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I * J)).ideal U ≤
        (I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have key := @derivIdeal_mul_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) (J.ideal U)
    have h1 : (derivIdealSheaf k p (I * J)).ideal U =
        @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U * J.ideal U) := by
      rw [derivIdealSheaf_ideal, hmul]
    have h2 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) =
        (derivIdealSheaf k p I).ideal U := (derivIdealSheaf_ideal k p I U).symm
    have h3 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (J.ideal U) =
        (derivIdealSheaf k p J).ideal U := (derivIdealSheaf_ideal k p J U).symm
    rw [h1]
    refine key.trans (sup_le ?_ ?_)
    · rw [h3, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_left U
    · rw [h2, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_right U
  exact h

theorem derivIdealSheaf_pow_succ_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I ^ (n + 1))).ideal U ≤ (I ^ n * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have hpow : ∀ m : ℕ, (I ^ m).ideal U = I.ideal U ^ m := fun m =>
      congrFun (Scheme.IdealSheafData.ideal_pow I m) U
    rw [hmul, derivIdealSheaf_ideal, derivIdealSheaf_ideal, hpow, hpow]
    exact @derivIdeal_pow_succ_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) n
  exact key

noncomputable def derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => derivIdealSheaf k p (derivIdealSheafIterate k p r I)

@[simp] theorem derivIdealSheafIterate_zero (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) : derivIdealSheafIterate k p 0 I = I :=
  rfl

theorem derivIdealSheafIterate_succ (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + 1) I = derivIdealSheaf k p (derivIdealSheafIterate k p r I) :=
  rfl

theorem derivIdealSheafIterate_one (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    derivIdealSheafIterate k p 1 I = derivIdealSheaf k p I :=
  rfl

theorem derivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r s : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + s) I =
      derivIdealSheafIterate k p r (derivIdealSheafIterate k p s I) := by
  induction r with
  | zero => rw [Nat.zero_add, derivIdealSheafIterate_zero]
  | succ n ih =>
      rw [add_right_comm, derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih]

@[simp] theorem derivIdealSheafIterate_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [derivIdealSheafIterate_zero,
        @derivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)]
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheaf_ideal, ih,
        @derivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) n (I.ideal U)]

theorem le_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivIdealSheafIterate_succ]
    exact le_trans ih (le_derivIdealSheaf k p (derivIdealSheafIterate k p n I))

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealLocalization
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

private theorem derivation_mem_map_of_forall_mem {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra R B]
    (D' : Derivation R B B) {P : Ideal A}
    (hgen : ∀ p ∈ P, D' (algebraMap A B p) ∈ P.map (algebraMap A B)) :
    ∀ x ∈ P.map (algebraMap A B), D' x ∈ P.map (algebraMap A B) := by
  intro x hx
  have hx' : x ∈ Ideal.span ((algebraMap A B) '' (P : Set A)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hgen p hp
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D' (y + z) = D' y + D' z := by simp
      rw [h]
      exact Ideal.add_mem _ ihy ihz
  | smul a y hy ih =>
      have hy' : y ∈ P.map (algebraMap A B) := hy
      rw [smul_eq_mul, D'.leibniz]
      simp only [smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy')

private theorem derivation_smul_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (c : A) (D₀ : Derivation R A A) (x : A) : (c • D₀) x = c * D₀ x := rfl

private theorem mul_derivation_mem_of_span_eq {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {G : Set A} {P : Ideal A} (hP : Ideal.span G = P) (D₀ : Derivation R A A)
    (c : A) (hG : ∀ g ∈ G, c * D₀ g ∈ P) : ∀ x ∈ P, c * D₀ x ∈ P := by
  intro x hx
  rw [← hP] at hx
  induction hx using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D₀ (y + z) = D₀ y + D₀ z := by simp
      rw [h, mul_add]
      exact P.add_mem ihy ihz
  | smul a y hy ih =>
      have hyP : y ∈ P := by rw [← hP]; exact hy
      rw [smul_eq_mul, D₀.leibniz]
      simp only [smul_eq_mul, mul_add]
      refine P.add_mem ?_ ?_
      · have h1 : c * (a * D₀ y) = a * (c * D₀ y) := by ring
        rw [h1]
        exact P.mul_mem_left a ih
      · exact P.mul_mem_left c (P.mul_mem_right (D₀ a) hyP)

private theorem exists_mem_mul_algebraMap_eq_of_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx
  exact ⟨u.1, u.2, u.1.2, hu⟩

private theorem exists_mul_mem_of_algebraMap_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (P : Ideal A) {y : A}
    (hy : algebraMap A B y ∈ P.map (algebraMap A B)) :
    ∃ m : M, (m : A) * y ∈ P := by
  obtain ⟨p, t, hp, h⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M P hy
  have h2 : algebraMap A B (y * (t : A)) = algebraMap A B p := by
    rw [map_mul]; linear_combination h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := B)).mp h2
  refine ⟨c * t, ?_⟩
  have heq : ((c * t : M) : A) * y = (c : A) * p := by
    push_cast
    linear_combination hc
  rw [heq]
  exact P.mul_mem_left _ hp

theorem mapToLocalization_mem_tangentDerivations (M : Submonoid S) [IsLocalization M S']
    {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by
  have hD' := (mem_tangentDerivations k P D).mp hD
  rw [mem_tangentDerivations]
  refine derivation_mem_map_of_forall_mem (D.mapToLocalization (S' := S') M) ?_
  intro p hp
  rw [Derivation.mapToLocalization_algebraMap]
  exact Ideal.mem_map_of_mem _ (hD' p hp)

theorem map_logDerivIdeal_le (M : Submonoid S) [IsLocalization M S'] (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)
  · intro D hD x hx
    rw [Ideal.mem_comap]
    have h : algebraMap S S' (D x) =
        (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
      rw [Derivation.mapToLocalization_algebraMap]
    rw [h]
    exact derivation_apply_mem_logDerivIdeal k _ _ _
      (mapToLocalization_mem_tangentDerivations (S' := S') k M hD)
      (Ideal.mem_map_of_mem _ hx)

theorem exists_mem_tangentDerivations_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by
  have hDt := (mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD
  obtain ⟨m₀, D₀, hD₀⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    · have hgP : g ∈ P := by
        rw [← hG]
        exact Ideal.subset_span (Finset.mem_coe.mpr hg)
      have h1 : algebraMap S S' g ∈ P.map (algebraMap S S') := Ideal.mem_map_of_mem _ hgP
      have h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S') := hDt _ h1
      have h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S') := by
        rw [← hD₀ g]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨n, hn⟩ := exists_mul_mem_of_algebraMap_mem_map M P h3
      exact ⟨n, fun _ => hn⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by
    refine ⟨Finset.prod G (fun g => ((f g : S))),
      Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg
    have h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ (hf g hg)
  refine ⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩
  · have hgen : ∀ g ∈ (↑G : Set S), c * D₀ g ∈ P := fun g hg => hcP g (Finset.mem_coe.mp hg)
    rw [mem_tangentDerivations]
    intro x hx
    have h := mul_derivation_mem_of_span_eq hG D₀ c hgen x hx
    rw [derivation_smul_apply]
    exact h
  · intro s
    show algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s)
        = algebraMap S S' ((c • D₀) s)
    rw [derivation_smul_apply, map_mul, map_mul, mul_assoc, hD₀ s]

theorem logDerivIdeal_map_le_map_logDerivIdeal (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩
  intro D hD x hx
  obtain ⟨m, D₁, hD₁, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨y, t, hy, hxt⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M J hx
  have hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S') :=
    Ideal.map_mono (le_logDerivIdeal k P J) hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp only [smul_eq_mul] at h1
  have e1 := hm y
  have e2 := hm (t : S)
  have hmul : algebraMap S S' ((m : S) * (t : S)) * D x
      = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + e1 - x * e2
  have hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    refine sub_mem ?_ ?_
    · exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)
    · exact Ideal.mul_mem_right _ _ hxL
  have hu : IsUnit (algebraMap S S' ((m : S) * (t : S))) := by
    rw [map_mul]
    exact (IsLocalization.map_units (M := M) (S := S') m).mul
      (IsLocalization.map_units (M := M) (S := S') t)
  obtain ⟨u, hu'⟩ := hu
  have hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' ((m : S) * (t : S)) * D x) := by
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  rw [hrw]
  exact Ideal.mul_mem_left _ _ hmem

theorem logDerivIdeal_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)

theorem logDerivIdealIterate_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]

theorem logDerivIdeal_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  logDerivIdeal_map k (Submonoid.powers g) hP J

theorem logDerivIdealIterate_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) :=
  logDerivIdealIterate_map k (Submonoid.powers g) hP r J

end FunctorialResolution.EmbeddedResolution
end
