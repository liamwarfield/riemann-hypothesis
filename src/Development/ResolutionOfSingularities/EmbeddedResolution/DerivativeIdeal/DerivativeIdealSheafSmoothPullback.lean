module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LeadingForm
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem sectionsAlgebraMap_comp_appLE (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) :
    (h.appLE W V e).hom.comp (sectionsAlgebraMap k p W) = sectionsAlgebraMap k (h ≫ p) V := by
  rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

theorem sectionsAlgebraMap_appLE_apply (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) (a : k) :
    (h.appLE W V e).hom (sectionsAlgebraMap k p W a) = sectionsAlgebraMap k (h ≫ p) V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a

private theorem exists_pow_mul_mem_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (N : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ N.map (algebraMap R S)) : ∃ n : ℕ, f ^ n * x ∈ N := by
  obtain ⟨⟨a, t⟩, hmul⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers f) (S := S)).mp hx
  have hmul' : algebraMap R S (x * (t : R)) = algebraMap R S (a : R) := by
    rw [map_mul]
    exact hmul
  obtain ⟨c, hceq⟩ :=
    (IsLocalization.eq_iff_exists (M := Submonoid.powers f) (S := S)).mp hmul'
  obtain ⟨i, hi⟩ := t.2
  obtain ⟨j, hj⟩ := c.2
  have hi' : f ^ i = (t : R) := hi
  have hj' : f ^ j = (c : R) := hj
  refine ⟨i + j, ?_⟩
  have key : f ^ (i + j) * x = f ^ j * (x * f ^ i) := by ring
  rw [key, hi', hj', hceq]
  exact N.mul_mem_left _ a.2

private theorem idealSheafData_ideal_le_congr {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    {A B : Y.affineOpens} (hAB : A = B) (h : J₁.ideal B ≤ J₂.ideal B) :
    J₁.ideal A ≤ J₂.ideal A := by
  subst hAB
  exact h

private theorem idealSheafData_ideal_le_of_locally_le {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ ≤ J₂.ideal ⟨V, hV⟩) (U : Y.affineOpens) :
    J₁.ideal U ≤ J₂.ideal U := by
  intro x hx
  set s : Set Γ(Y, U.1) := {f : Γ(Y, U.1) | ∃ n : ℕ, f ^ n * x ∈ J₂.ideal U} with hs
  have hcover : U.1 ≤ ⨆ f : s, Y.basicOpen (f : Γ(Y, U.1)) := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := H z
    obtain ⟨f, g, hfg, hzf⟩ := exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩
    have hres : Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₁.ideal U)
        ≤ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₂.ideal U) := by
      rw [J₁.map_ideal_basicOpen U f, J₂.map_ideal_basicOpen U f]
      have hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U := ⟨V, hV⟩) g := Subtype.ext hfg
      refine idealSheafData_ideal_le_congr J₁ J₂ hABO ?_
      rw [← J₁.map_ideal_basicOpen ⟨V, hV⟩ g, ← J₂.map_ideal_basicOpen ⟨V, hV⟩ g]
      exact Ideal.map_mono hle
    have hfs : f ∈ s := by
      have := U.2.isLocalization_basicOpen f
      rw [hs]
      refine exists_pow_mul_mem_of_mem_map (S := Γ(Y, Y.basicOpen f)) f (J₂.ideal U) x ?_
      have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f))
          = (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
      rw [halg]
      exact hres (Ideal.mem_map_of_mem _ hx)
    exact Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩
  have hspan : Ideal.span s = ⊤ := (U.2.self_le_iSup_basicOpen_iff).mp hcover
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J₂.ideal U) s hspan x ?_
  rintro ⟨f, hf⟩
  rw [hs] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

private theorem idealSheafData_eq_of_locally_eq {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ = J₂.ideal ⟨V, hV⟩) : J₁ = J₂ := by
  have key : ∀ U : Y.affineOpens, J₁.ideal U = J₂.ideal U := by
    intro U
    refine le_antisymm (idealSheafData_ideal_le_of_locally_le J₁ J₂ ?_ U)
      (idealSheafData_ideal_le_of_locally_le J₂ J₁ ?_ U)
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.le⟩
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.ge⟩
  exact Scheme.IdealSheafData.ext (funext key)

attribute [local instance] EtaleCoordinates.sumEvalAlgebra in
private theorem exists_affineOpen_derivIdealSheaf_comap_ideal_eq (k : Type u) [Field k] [IsNoetherianRing k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      (derivIdealSheaf k (h ≫ p) (I.comap h)).ideal ⟨V, hV⟩
        = ((derivIdealSheaf k p I).comap h).ideal ⟨V, hV⟩ := by
  classical
  obtain ⟨W₀, m, hxW₀, -, ⟨c₀⟩⟩ := exists_etaleChart p (h.base y)
  obtain ⟨W, V, d, e, hW, hV, hyV, hWW₀, -, g, hgE, hg⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W₀ hxW₀ ⊤ (by trivial)
  refine ⟨V, hV, hyV, ?_⟩
  have : Etale g := hgE
  let c : EtaleChart p W m := c₀.restrict hWW₀
  let instkS : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instkT : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  let instPS : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.algebra
  let instTow1 : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.isScalarTower
  have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    c.algebra_formallyEtale hW
  let instChartAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have instFE2 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  let instST : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let instTowkST : IsScalarTower k Γ(X, W) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (sectionsAlgebraMap_appLE_apply k p h W V e a).symm
  let instScalarTowerChart : IsScalarTower Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_isScalarTower hW h e g hg
  let instSumT : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    ((algebraMap (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)).comp
      (algebraMap (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)))).toAlgebra
  let instScalarTowerSum : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTowkSum : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := by
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) :=
      EtaleCoordinates.sumEvalAlgebra_isScalarTower k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W)
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) a),
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      IsScalarTower.algebraMap_apply k Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      ← IsScalarTower.algebraMap_apply k Γ(X, W) Γ(Y, V)]
  have instFE3 : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W) Γ(Y, V)
  have hcoord : ∀ i : ULift.{u} (Fin m),
      algebraMap Γ(X, W) Γ(Y, V) (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W) i)
        = EtaleCoordinates.coord k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V)
            (Sum.inl i) := by
    intro i
    rw [EtaleCoordinates.coord_def k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i),
      IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W),
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]
  simp only [derivIdealSheaf_ideal]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]
  exact (EtaleCoordinates.map_derivIdeal_sum k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
    Γ(X, W) Γ(Y, V) hcoord (I.ideal ⟨W, hW⟩)).symm

theorem derivIdealSheaf_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) :
    derivIdealSheaf k (h ≫ p) (I.comap h) = (derivIdealSheaf k p I).comap h :=
  idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h I y

theorem derivIdealSheafIterate_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k (h ≫ p) r (I.comap h) = (derivIdealSheafIterate k p r I).comap h := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
      derivIdealSheaf_comap k p h (derivIdealSheafIterate k p r I)]

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace EtaleCoordinates

theorem partialDeriv_comm (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallyEtale (MvPolynomial ι k) T]
    (i j : ι) (a : T) :
    partialDeriv k ι T i (partialDeriv k ι T j a)
      = partialDeriv k ι T j (partialDeriv k ι T i a) := by
  have hzero : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ = (0 : Derivation k T T) := by
    refine derivation_ext_of_coord k ι T T _ _ ?_
    intro l
    rw [Derivation.commutator_apply]
    simp only [partialDeriv_coord]
    split_ifs <;> simp
  have h2 : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ a = 0 := by
    rw [hzero]; simp
  rw [Derivation.commutator_apply] at h2
  linear_combination h2

end EtaleCoordinates

private theorem exists_commuting_dual_derivations (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (A : Type*) [CommRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    (e : Module.Basis ι A (KaehlerDifferential k A)) (w : ι → A)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (w i))) :
    ∃ D : ι → Derivation k A A,
      (∀ i j : ι, D i (w j) = if i = j then 1 else 0) ∧
      (∀ i j : ι, ∀ a : A, D i (D j a) = D j (D i a)) := by
  let _ : Algebra (MvPolynomial ι k) A :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] A).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      simp [MvPolynomial.algebraMap_eq]
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e w hdet
  have hcoord : ∀ i : ι, EtaleCoordinates.coord k ι A i = w i := by
    intro i
    rw [EtaleCoordinates.coord_def, RingHom.algebraMap_toAlgebra]
    simp
  refine ⟨fun i => EtaleCoordinates.partialDeriv k ι A i, ?_, ?_⟩
  · intro i j
    rw [← hcoord j]
    exact EtaleCoordinates.partialDeriv_coord k ι A i j
  · intro i j a
    exact EtaleCoordinates.partialDeriv_comm k ι A i j a

theorem exists_regularParameters_of_formallyEtale (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    ∃ (h : ℕ) (x : Fin h → A) (D : Fin h → Derivation k A A),
      Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A ∧
      (∀ i j : Fin h, D i (x j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : A, D i (D j a) = D j (D i a)) := by
  obtain ⟨g, w, J, hgq, -, hspan, -, hgdet, -⟩ :=
    EtaleCoordinates.exists_adapted_parameters k ι S q A
  let _ : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have halg : (algebraMap (MvPolynomial ι k) A)
      = (algebraMap S A).comp (algebraMap (MvPolynomial ι k) S) := rfl
  have : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S,
        ← IsScalarTower.algebraMap_apply k S A]
  have : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have : Algebra.FormallySmooth k A := Algebra.FormallySmooth.comp k (MvPolynomial ι k) A
  obtain ⟨e, he⟩ : ∃ e : Module.Basis ι A (KaehlerDifferential k A),
      IsUnit (e.det fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) := by
    refine ⟨EtaleCoordinates.basisKaehler k ι A, ?_⟩
    rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S A w, ← hgdet]
    exact IsLocalization.map_units (M := q.primeCompl) A ⟨g, hgq⟩
  obtain ⟨D, hD, hDD⟩ :=
    exists_commuting_dual_derivations k ι A e (fun i => algebraMap S A (w i)) he
  obtain ⟨h, ix, hix, hrange⟩ :
      ∃ (h : ℕ) (ix : Fin h → ι), Function.Injective ix ∧ Set.range ix = (↑J : Set ι) := by
    refine ⟨J.card, fun i => ((J.equivFin.symm i : {a : ι // a ∈ J}) : ι), ?_, ?_⟩
    · intro a b hab
      exact J.equivFin.symm.injective (Subtype.ext hab)
    · ext l
      simp only [Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨i, rfl⟩
        exact (J.equivFin.symm i).2
      · intro hl
        exact ⟨J.equivFin ⟨l, hl⟩, by simp⟩
  have hset : (algebraMap S A) '' (w '' (↑J : Set ι))
      = Set.range fun i => algebraMap S A (w (ix i)) := by
    rw [← hrange]
    ext a
    constructor
    · rintro ⟨b, ⟨l, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨w (ix i), ⟨ix i, ⟨i, rfl⟩, rfl⟩, rfl⟩
  refine ⟨h, fun i => algebraMap S A (w (ix i)), fun i => D (ix i), ?_, ?_, ?_⟩
  · rw [← hspan, Ideal.map_span, hset]
  · intro i j
    rw [hD]
    simp only [show (ix i = ix j) ↔ (i = j) from ⟨fun hc => hix hc, fun hc => by rw [hc]⟩]
  · intro i j a
    exact hDD (ix i) (ix j) a

theorem exists_regularParameters_stalk_of_smooth (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x;
    ∃ (h : ℕ) (y : Fin h → X.presheaf.stalk x)
      (D : Fin h → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (∀ i j : Fin h, D i (y j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : X.presheaf.stalk x, D i (D j a) = D j (D i a)) := by
  let _ := stalkAlgebra k p x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  let _ := sectionsAlgebra k p U
  let _ := c.algebra
  let _ : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  have := c.algebra_formallyEtale hU
  have := c.isScalarTower
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsLocalization ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal).primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have := isNoetherianRing_stalk k p x
  let _ : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      rfl
  have := formallySmooth_residueField k p x rfl
  exact exists_regularParameters_of_formallyEtale k (ULift.{u} (Fin m)) Γ(X, U)
    ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)

theorem orderAt_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I J : X.IdealSheafData) (x : X) :
    orderAt (I * J) x = orderAt I x + orderAt J x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_mul]
  exact idealOrder_mul y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) (stalkIdeal J x)

theorem orderAt_pow (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (c : ℕ) (x : X) :
    orderAt (I ^ c) x = (c : ℕ∞) * orderAt I x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp only [orderAt_eq_idealOrder, stalkIdeal_pow]
  exact idealOrder_pow y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) c

theorem natCast_mul_le_mul_iff {c : ℕ} (hc : 1 ≤ c) (m : ℕ) (a : ℕ∞) :
    (c : ℕ∞) * (m : ℕ∞) ≤ (c : ℕ∞) * a ↔ (m : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
    have hc0 : (c : ℕ∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have htop : (c : ℕ∞) * ⊤ = ⊤ := by simp [hc0]
    simp [htop]
  | coe n =>
    constructor
    · intro hle
      have h' : c * m ≤ c * n := by exact_mod_cast hle
      have h'' : m ≤ n := Nat.le_of_mul_le_mul_left h' (by omega)
      exact_mod_cast h''
    · intro hle
      have h' : m ≤ n := by exact_mod_cast hle
      have h'' : c * m ≤ c * n := Nat.mul_le_mul (le_refl c) h'
      exact_mod_cast h''

theorem orderAtLeastLocus_pow_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    orderAtLeastLocus (I ^ c) (c * m) = orderAtLeastLocus I m := by
  ext x
  rw [mem_orderAtLeastLocus_iff, mem_orderAtLeastLocus_iff, orderAt_pow k p I c x, Nat.cast_mul]
  exact natCast_mul_le_mul_iff hc m (orderAt I x)

end FunctorialResolution.EmbeddedResolution
end
