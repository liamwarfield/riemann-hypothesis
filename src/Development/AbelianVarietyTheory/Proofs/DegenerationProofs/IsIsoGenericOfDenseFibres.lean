module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowSmulKerEqZeroOfDense
open Module
open TensorProduct

namespace GlobalTheory

namespace GenericFreeness

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem IsBasisAway.exists_basis_apply_eq {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) :
    ∃ b : Module.Basis s (Localization.Away a) (Localization.Away a ⊗[R] M),
      ∀ x : s, b x = 1 ⊗ₜ (x : M) := by
  let f := TensorProduct.mk R (Localization.Away a) M 1
  refine ⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M))
    (LinearIndependent.of_isLocalizedModule (Localization.Away a) (.powers a) f h.linearIndepOn)
    ?_, fun x => Module.Basis.mk_apply _ _ x⟩
  intro y _
  induction y with
  | add y z hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | tmul c m =>
    obtain ⟨n, hn⟩ := h.2.2 m trivial
    rw [bot_sup_eq] at hn
    have h1 := Submodule.mem_map_of_mem (f := f) hn
    rw [Submodule.map_span] at h1
    have h2 := Submodule.span_subset_span R (Localization.Away a) _ h1
    obtain ⟨u, hu⟩ :=
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow n).exists_left_inv
    have e : c ⊗ₜ[R] m = (c * u) • f (a ^ n • m) := by
      simp only [f, TensorProduct.mk_apply, ← smul_tmul, smul_tmul', smul_eq_mul,
        Algebra.smul_def, map_pow, mul_one, mul_assoc, hu]
    rw [e, Set.range_comp, Subtype.range_coe]
    exact Submodule.smul_mem _ _ h2

theorem IsBasisAway.one_tmul_ne_zero {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (K : Type*) [CommRing K] [Nontrivial K]
    [Algebra R K] (ha : IsUnit (algebraMap R K a)) {x : M} (hx : x ∈ s) :
    (1 : K) ⊗ₜ[R] x ≠ 0 := by
  obtain ⟨b, hb⟩ := h.exists_basis_apply_eq
  letI : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) K :=
    .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm
  have := ((b.baseChange K).map (AlgebraTensorModule.cancelBaseChange R _ K K M)).ne_zero ⟨x, hx⟩
  simpa [hb] using this

end GenericFreeness

open GenericFreeness

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
  {A : Type*} [CommRing A] [Algebra R A] (φ : A₀ →ₐ[R] A)

theorem exists_pow_smul_ker_eq_zero_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A₀, φ y = 0 → ∃ n : ℕ, a ^ n • y = 0 := by
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  let J : Ideal A₀ := RingHom.ker φ
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := A₀) J
  obtain ⟨b, hb0, hb⟩ := exists_hasBasisAway_quotient R A₀ A₀ J (IsNoetherian.noetherian J)
  have ha1 := HasBasisAway.map (a := a) (J.subtype.restrictScalars R) ⊥ (by
    have : Submodule.comap (J.subtype.restrictScalars R) ⊥ = ⊥ :=
      LinearMap.ker_eq_bot.2 Subtype.val_injective
    rwa [this])
  have e : (⊥ : Submodule R A₀) ⊔ LinearMap.range (J.subtype.restrictScalars R) =
      J.restrictScalars R := by
    rw [bot_sup_eq]
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [e] at ha1
  obtain ⟨s, hs⟩ := ha1.of_dvd (dvd_mul_right a b)
  obtain ⟨t, ht⟩ := hb.of_dvd (dvd_mul_left b a)
  have hst := hs.union bot_le le_top ht
  have hab := mul_ne_zero ha0 hb0
  obtain ⟨x, hxD, hxa⟩ := hD.exists_mem_open (PrimeSpectrum.basicOpen (a * b)).isOpen
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hab⟩
  have hu : IsUnit (algebraMap R x.asIdeal.ResidueField (a * b)) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hxa
  obtain rfl : s = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
    refine hst.one_tmul_ne_zero _ hu (Or.inl hy) (h x hxD ?_)
    have : φ y = 0 := hs.1 hy
    rw [Algebra.TensorProduct.map_tmul, this, tmul_zero, map_zero]
  refine ⟨a * b, hab, fun y hy => ?_⟩
  simpa using hs.2.2 y hy

theorem exists_baseChange_injective_of_dense.{w} {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'] [Module.Flat R R'],
      IsUnit (algebraMap R R' a) →
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R') φ) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense φ hD h
  refine ⟨a, ha0, fun R' _ _ _ hu => (injective_iff_map_eq_zero _).2 fun z hz => ?_⟩
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ.toLinearMap)
  obtain ⟨w, rfl⟩ := (hex z).1 hz
  clear hz
  induction w with
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]
  | tmul c y =>
    obtain ⟨n, hn⟩ := ha y y.2
    obtain ⟨u, hu⟩ := (hu.pow n).exists_left_inv
    have e : c = a ^ n • (c * u) := by
      rw [Algebra.smul_def, map_pow, mul_comm, mul_assoc, hu, mul_one]
    rw [LinearMap.lTensor_tmul, e, smul_tmul, Submodule.subtype_apply, hn, tmul_zero]

end

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace GlobalTheory

namespace GenericIso

theorem isIso_iff_of_isPullback {P X' Y X : Scheme.{0}} {a : P ⟶ X'} {b : P ⟶ Y} {h : X' ⟶ X}
    {g : Y ⟶ X} (H : IsPullback a b h g) : IsIso b ↔ IsIso (pullback.snd h g) := by
  rw [← H.isoPullback_hom_snd, isIso_comp_left_iff]

theorem isIso_snd_comp {X' Y X Z : Scheme.{0}} (h : X' ⟶ X) (g : Y ⟶ X) (k : Z ⟶ Y)
    (H : IsIso (pullback.snd h g)) : IsIso (pullback.snd h (k ≫ g)) := by
  have := (IsPullback.of_hasPullback (pullback.snd h g) k).paste_horiz
    (IsPullback.of_hasPullback h g)
  exact (isIso_iff_of_isPullback this).1 inferInstance

theorem isPullback_over {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsPullback (pullback.fst X'.hom t) ((Over.pullback t).map h).left h.left
      (pullback.fst X.hom t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback X.hom t)
  · have e : ((Over.pullback t).map h).left ≫ pullback.snd X.hom t = pullback.snd X'.hom t :=
      pullback.lift_snd _ _ _
    rw [e, Over.w h]
    exact IsPullback.of_hasPullback X'.hom t
  · exact (pullback.lift_fst _ _ _).symm

theorem isIso_over_iff {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsIso ((Over.pullback t).map h) ↔ IsIso (pullback.snd h.left (pullback.fst X.hom t)) := by
  rw [← isIso_iff_of_isPullback (isPullback_over t h)]
  exact (isIso_iff_of_reflects_iso _ (Over.forget T)).symm

section Affine

variable {R A₀ A : Type} [CommRing R] [CommRing A₀] [CommRing A] [Algebra R A₀] [Algebra R A]
  (f : A₀ →ₐ[R] A) (B : Type) [CommRing B] [Algebra R B]

theorem isPullback_tensor (A : Type) [CommRing A] [Algebra R A] :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B A)).flip

theorem isPullback_tensor_map :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R B) f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom)) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_tensor B A₀)
  · convert isPullback_tensor (R := R) B A using 1
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

theorem isIso_spec_iff {C D : Type} [CommRing C] [CommRing D] (φ : C →+* D) :
    IsIso (Spec.map (CommRingCat.ofHom φ)) ↔ Function.Bijective φ := by
  rw [isIso_SpecMap_iff]
  rfl

theorem bijective_of_faithfullyFlat (C : Type) [CommRing C] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [Module.FaithfullyFlat B C]
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R C) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) f) := by
  have e : LinearMap.lTensor C (f.toLinearMap.baseChange B) =
      ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B C f.toLinearMap) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R B B C A₀).toLinearMap := by
    ext
    simp
  have h1 : Function.Bijective (LinearMap.lTensor C (f.toLinearMap.baseChange B)) := by
    rw [e]
    exact ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.bijective.comp H).comp
      (AlgebraTensorModule.cancelBaseChange R B B C A₀).bijective
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective B C _).1 h1

theorem bijective_residueField (K : Type) [Field K] [Algebra R K] (x : PrimeSpectrum R)
    (hx : x.asIdeal = RingHom.ker (algebraMap R K))
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) f) := by
  have h1 : x.asIdeal ≤ RingHom.ker (algebraMap R K) := hx.le
  have h2 : x.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := fun r hr => by
    change IsUnit (algebraMap R K r)
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hr (hx.ge h0)
  let : Algebra x.asIdeal.ResidueField K :=
    (Ideal.ResidueField.lift x.asIdeal (algebraMap R K) h1 h2).toAlgebra
  have : IsScalarTower R x.asIdeal.ResidueField K :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap _ _ h1 h2 r).symm
  exact bijective_of_faithfullyFlat f _ K H

end Affine

end GenericIso

open GenericIso

theorem isIso_generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X' X : Over (Sp R))
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      (h : X' ⟶ X) [IsAffineHom h.left] (Sg : Set (Sp R)), Dense Sg →
      (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
        IsIso ((Over.pullback t).map h)) → IsIso ((Over.pullback (Out.jK R)).map h) := by
  intro R _ _ _ X' X _ _ _ h _ Sg hD H
  rw [isIso_over_iff]
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _)
    (X.left.affineCover.pullback₁ (pullback.fst X.hom (Out.jK R))) fun (i : X.left.affineCover.I₀) => ?_

  obtain ⟨A₀, u, hu₀, ⟨e, he⟩⟩ : ∃ (A₀ : CommRingCat.{0}) (u : Spec A₀ ⟶ X.left)
      (_ : IsOpenImmersion u), ∃ e : X.left.affineCover.X i ⟶ Spec A₀,
      e ≫ u = X.left.affineCover.f i :=
    ⟨_, (X.left.affineCover.X i).isoSpec.inv ≫ X.left.affineCover.f i, inferInstance,
      (X.left.affineCover.X i).isoSpec.hom, by simp⟩
  have : IsAffine (pullback h.left u) := isAffine_of_isAffineHom (pullback.snd h.left u)
  obtain ⟨A, j, hj, f, sq⟩ : ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X'.left)
      (_ : IsOpenImmersion j) (f : A₀ ⟶ A), IsPullback j (Spec.map f) h.left u := by
    obtain ⟨f, hf⟩ := Spec.map_surjective
      ((pullback h.left u).isoSpec.inv ≫ pullback.snd h.left u)
    refine ⟨_, (pullback h.left u).isoSpec.inv ≫ pullback.fst h.left u, inferInstance, f, ?_⟩
    rw [hf]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩
      (pullback h.left u).isoSpec.symm rfl rfl
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ X.hom)
  let : Algebra R A₀ := φ.hom.toAlgebra
  let : Algebra R A := (φ ≫ f).hom.toAlgebra
  let F : A₀ →ₐ[R] A := ⟨f.hom, fun _ => rfl⟩
  have : Algebra.FiniteType R A₀ := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map (φ ≫ f)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, ← sq.w, Category.assoc, Over.w h]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = u ≫ X.hom := hφ
  have key : ∀ (B : Type) [CommRing B] [Algebra R B],
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) F) ↔
      IsIso (pullback.snd h.left (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom) ≫ u)) := by
    intro B _ _
    rw [← isIso_iff_of_isPullback ((isPullback_tensor_map F B).paste_horiz sq), isIso_spec_iff]
    rfl
  have hfib : ∀ x : PrimeSpectrum R, x ∈ (Sg : Set (PrimeSpectrum R)) → Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) F) := by
    intro x hx
    obtain ⟨K, _, t, ht, hiso⟩ := H x hx
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
    let : Algebra R K := ψ.hom.toAlgebra
    refine bijective_residueField F K x ?_ ((key K).2 ?_)
    · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
        ht.le (Set.mem_range_self _)
      rw [← this]
      rfl
    · have w := (isPullback_tensor (R := R) K A₀).w
      rw [hφ', ← Category.assoc] at w
      have := isIso_snd_comp _ _ (pullback.lift _ _ w) ((isIso_over_iff _ h).1 hiso)
      rwa [pullback.lift_fst] at this
  obtain ⟨a, ha0, ha⟩ := exists_baseChange_injective_of_dense.{0} F hD fun x hx => (hfib x hx).1
  obtain ⟨b, hb0, hb⟩ := exists_baseChange_surjective_of_dense.{0} F hD fun x hx => (hfib x hx).2
  have hu : ∀ c : R, c ≠ 0 → IsUnit (algebraMap R (FractionRing R) c) := fun c hc =>
    IsLocalization.map_units (M := nonZeroDivisors R) _ ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩
  have hK := (key (FractionRing R)).1 ⟨ha _ (hu a ha0), hb _ (hu b hb0)⟩
  let q := pullback.fst X.hom (Out.jK R)
  have w : (pullback.snd q (X.left.affineCover.f i) ≫ e) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀)) =
      (pullback.fst q (X.left.affineCover.f i) ≫ pullback.snd X.hom (Out.jK R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hφ', Category.assoc, reassoc_of% he, ← pullback.condition_assoc, Category.assoc,
      pullback.condition]
  have h3 := isIso_snd_comp _ _ ((isPullback_tensor (R := R) (FractionRing R) A₀).lift _ _ w) hK
  rw [IsPullback.lift_fst_assoc, Category.assoc, he, ← pullback.condition] at h3
  have sq2 := (IsPullback.of_hasPullback (pullback.snd h.left q)
    (pullback.fst q (X.left.affineCover.f i))).paste_horiz (IsPullback.of_hasPullback h.left q)
  exact (isIso_iff_of_isPullback sq2).2 h3

end GlobalTheory
