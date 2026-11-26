module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSectionStalk
private lemma UpperTheory.isLocalHom_of_square_zero {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x * x = 0) : IsLocalHom π := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hs c
  have h0 : π (a * b - 1) = 0 := by rw [map_sub, map_mul, hc, map_one, sub_self]
  have hn : IsNilpotent (a * b - 1) := ⟨2, by rw [pow_two]; exact hk _ h0⟩
  have hu : IsUnit (a * b) := by simpa using hn.isUnit_add_one
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.formally_smooth_section_stalk :
    open AlgebraicGeometry CategoryTheory in
        ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ p : X,
          ∃ (B : CommRingCat.{0}) (α : X.presheaf.stalk p ⟶ B) (σ : B ⟶ X.presheaf.stalk p) (ι : Spec B ⟶ Y),
            α.hom.FormallySmooth ∧ α.hom.EssFiniteType ∧ Mono ι ∧
              ι ≫ f = Spec.map α ≫ X.fromSpecStalk p ∧ Spec.map σ ≫ ι = X.fromSpecStalk p ≫ s ∧
              ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R) (v : Spec R' ⟶ Y),
                Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
                  Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ ι := by
  open AlgebraicGeometry CategoryTheory in
  intro X Y f _ s hs p
  have hp : f (s p) = p := by
    rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hi : Inseparable p (f (s p)) := Inseparable.of_eq hp.symm
  have hfs : (f.stalkMap (s p)).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]; trivial
  have hft : (f.stalkMap (s p)).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f (s p)
  refine ⟨Y.presheaf.stalk (s p), (X.presheaf.stalkCongr hi).hom ≫ f.stalkMap (s p),
    s.stalkMap p, Y.fromSpecStalk (s p), ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hfs
  · exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr hft
  · have h : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk p =
        X.fromSpecStalk (f (s p)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.specializes'
    rw [Spec.map_comp, Category.assoc, h, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · exact Scheme.SpecMap_stalkMap_fromSpecStalk s
  · intro R R' _ π φ v hπ hk hv
    haveI : IsLocalHom π.hom := UpperTheory.isLocalHom_of_square_zero π.hom hπ hk
    haveI : IsLocalRing R' := π.hom.domain_isLocalRing
    have hsp : v (IsLocalRing.closedPoint R') ⤳ s p := by
      have h1 : v (IsLocalRing.closedPoint R') =
          s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) := by
        have h3 : v (Spec.map π (IsLocalRing.closedPoint R)) =
            s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) :=
          congrArg (fun k : Spec R ⟶ Y => k (IsLocalRing.closedPoint R)) hv
        exact (congrArg v (Spec_closedPoint (f := π)).symm).trans h3
      have h2 : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ⤳ p := by
        have : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ∈
            Set.range (X.fromSpecStalk p) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      rw [h1]
      exact h2.map s.continuous
    refine ⟨Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo v, ?_⟩
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSurjectiveDerivation
open TensorProduct in
private theorem UpperTheory.universal_derivation_surjective {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra B A] [IsScalarTower A B A]
    [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (d : Derivation A B (Fin n → A)), Function.Surjective d ∧
      ∀ (R : Type) [AddCommGroup R] [Module A R] [Module B R] [IsScalarTower B A R]
        (δ : Derivation A B R), ∃ c : Fin n → R, ∀ b, δ b = ∑ i, d b i • c i := by
  haveI : Module.Free A (A ⊗[B] Ω[B⁄A]) := Module.free_of_flat_of_isLocalRing
  let e := Module.finBasis A (A ⊗[B] Ω[B⁄A])
  let D0 : Derivation A B (A ⊗[B] Ω[B⁄A]) :=
    (TensorProduct.mk B A Ω[B⁄A] 1).compDer (KaehlerDifferential.D A B)
  have hD0 : ∀ b, D0 b = 1 ⊗ₜ KaehlerDifferential.D A B b := fun b => rfl
  have hsurj : Function.Surjective D0 := by
    have h1 : ∀ (w : Ω[B⁄A]) (a : A), a ⊗ₜ[B] w ∈ LinearMap.range D0.toLinearMap := by
      intro w
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        intro a
        have : a ⊗ₜ[B] KaehlerDifferential.D A B b = a • D0 b := by
          rw [hD0, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ ⟨b, rfl⟩
      | zero => intro a; simp
      | add x y _ _ hx hy =>
        intro a
        rw [TensorProduct.tmul_add]
        exact add_mem (hx a) (hy a)
      | smul b x _ hx =>
        intro a
        rw [← TensorProduct.smul_tmul]
        exact hx _
    intro x
    change x ∈ LinearMap.range D0.toLinearMap
    induction x with
    | tmul a w => exact h1 w a
    | add x y hx hy => exact add_mem hx hy
  refine ⟨_, (e.equivFun.toLinearMap.restrictScalars B).compDer D0,
    e.equivFun.surjective.comp hsurj, ?_⟩
  intro R _ _ _ _ δ
  haveI : IsScalarTower A B R := ⟨fun a b r => by
    rw [← algebraMap_smul A (a • b) r, ← algebraMap_smul A b r, ← mul_smul]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul]⟩
  let f : A ⊗[B] Ω[B⁄A] →ₗ[A] R := δ.liftKaehlerDifferential.liftBaseChange A
  refine ⟨fun i => f (e i), fun b => ?_⟩
  have h2 : δ b = f (D0 b) := by
    simp [f, hD0]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← e.sum_equivFun (D0 b), map_sum]
  simp only [map_smul]
  rfl

theorem UpperTheory.formally_smooth_surjective_derivation :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] (α : A →+* B) (σ : B →+* A),
        σ.comp α = RingHom.id A → α.FormallySmooth → α.EssFiniteType →
          ∃ (n : ℕ) (d : B → Fin n → A), Function.Surjective d ∧
            ∀ (R : Type) [CommRing R] (φ : A →+* R),
              (∀ c : Fin n → R, ∃ g : B →+* DualNumber R,
                (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (σ b)) ∧
                  ∀ b, (g b).snd = ∑ i, φ (d b i) * c i) ∧
              ∀ g : B →+* DualNumber R, (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (σ b)) →
                ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i := by
  intro A B _ _ _ α σ hσ hfs hft
  have hσ' : ∀ a, σ (α a) = a := fun a => RingHom.congr_fun hσ a
  letI : Algebra A B := α.toAlgebra
  letI : Algebra B A := σ.toAlgebra
  haveI : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hσ' a).symm
  haveI : Algebra.FormallySmooth A B := hfs
  haveI : Algebra.EssFiniteType A B := hft
  obtain ⟨n, d, hd, H⟩ := UpperTheory.universal_derivation_surjective (A := A) (B := B)
  have hmul : ∀ x y i, d (x * y) i = σ x * d y i + σ y * d x i := fun x y i => by
    rw [d.leibniz]; rfl
  have hα : ∀ a, d (α a) = 0 := fun a => d.map_algebraMap a
  refine ⟨n, d, hd, fun R _ φ => ⟨fun c => ?_, fun g hg1 hg2 => ?_⟩⟩
  · refine ⟨{ toFun := fun b => TrivSqZeroExt.inl (φ (σ b)) +
                TrivSqZeroExt.inr (∑ i, φ (d b i) * c i)
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
    · ext <;> simp
    · intro x y
      ext
      · simp
      · simp [hmul, -Derivation.leibniz, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, mul_add, add_comm]
    · ext <;> simp
    · intro x y
      ext <;> simp [add_mul, Finset.sum_add_distrib]
    · intro a
      simp [hα, hσ']
    · intro b
      simp
    · intro b
      simp
  · letI : Algebra A R := φ.toAlgebra
    letI : Algebra B R := (φ.comp σ).toAlgebra
    haveI : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun b => rfl
    let δ : Derivation A B R := Derivation.mk'
      { toFun := fun b => (g b).snd
        map_add' := fun x y => by simp
        map_smul' := fun a b => by
          change (g (α a * b)).snd = φ a * (g b).snd
          simp [hg1] }
      (fun x y => by
        change (g (x * y)).snd = φ (σ x) * (g y).snd + φ (σ y) * (g x).snd
        simp [hg2, mul_comm])
    exact H R δ
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanLinearIndependentBase
theorem UpperTheory.span_linear_independent_base :
    ∀ {A Ω C E V I : Type} [CommRing A] [Field Ω] [Field C] [AddCommGroup E] [Module Ω E] [AddCommGroup V]
          [Module C V] [Fintype I] {n : ℕ} (φ : A →+* Ω) (ψ : A →+* C) (κ : E ≃ₗ[Ω] (Fin n → Ω)) (κ' : V ≃ₗ[C] (Fin n → C))
          (F : I → E), Function.Injective φ → LinearIndependent Ω F →
          Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)} =
            Submodule.span (↥φ.range) (Set.range F) →
          ∃ y : Module.Basis I C V, ∀ j, ∃ a : Fin n → A, (κ (F j) = fun i => φ (a i)) ∧ κ' (y j) = fun i => ψ (a i) := by
  intro A Ω C E V I _ _ _ _ _ _ _ _ n φ ψ κ κ' F hφ hF hspan
  classical
  have hlat : ∀ e ∈ Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)},
      ∃ a : Fin n → A, κ e = fun i => φ (a i) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, by ext i; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by ext i; simp [ha, hb]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, r, rfl⟩ := c
      refine ⟨r • a, ?_⟩
      change κ (φ r • x) = _
      ext i
      simp [ha]
  have ha : ∀ j, ∃ a : Fin n → A, κ (F j) = fun i => φ (a i) := fun j =>
    hlat _ (hspan ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose a ha using ha
  have hb : ∀ k : Fin n, ∃ b : I → A, ∀ i, ∑ j, a j i * b j = (1 : Matrix (Fin n) (Fin n) A) i k := by
    intro k
    have hk : κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) ∈
        Submodule.span (↥φ.range) (Set.range F) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨fun i => (1 : Matrix (Fin n) (Fin n) A) i k, by simp⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hk
    choose b hb using fun j => (c j).2
    refine ⟨b, fun i => hφ ?_⟩
    have h1 : ∑ j, φ (b j) • F j = κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) := by
      rw [← hc]
      exact Finset.sum_congr rfl fun j _ => by rw [hb j]; rfl
    have h2 := congrFun (congrArg κ h1) i
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    simp [ha, mul_comm]
  choose b hb using hb
  set P : Matrix (Fin n) I A := Matrix.of fun i j => a j i with hP
  set Q : Matrix I (Fin n) A := Matrix.of fun j k => b k j with hQ
  have hPQ : P * Q = 1 := by
    ext i k
    simpa [Matrix.mul_apply, hP, hQ] using hb k i
  have hQP : Q * P = 1 := by
    have hD : P * (Q * P - 1) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_one, sub_self]
    rw [← sub_eq_zero]
    generalize Q * P - 1 = D at hD
    ext l j
    have h0 : ∑ l, φ (D l j) • F l = 0 := by
      apply κ.injective
      ext i
      have h3 := congrArg φ (congrFun (congrFun hD i) j)
      simpa [Matrix.mul_apply, hP, ha, mul_comm] using h3
    apply hφ
    simpa using Fintype.linearIndependent_iff.1 hF _ h0 l
  have h1 : Q.map ψ * P.map ψ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h2 : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  refine ⟨(Pi.basisFun C I).map ((Matrix.toLin'OfInv h1 h2).trans κ'.symm), fun j => ⟨a j, ha j, ?_⟩⟩
  ext i
  simp [Matrix.toLin'OfInv, hP]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneLeftCongr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private noncomputable def UpperTheory.specMapOverOfAlgHom {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B : Type} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ x) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ x) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact f.comp_algebraMap)

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMapAlg_comp {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    UpperTheory.specMapOverOfAlgHom x g ≫ UpperTheory.specMapOverOfAlgHom x f = UpperTheory.specMapOverOfAlgHom x (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMap_id {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A : Type} [CommRing A] [Algebra R A] :
    UpperTheory.specMapOverOfAlgHom x (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private theorem UpperTheory.grpObj_one_left_congr {S : Scheme.{0}} (G : Over S) [GrpObj G]
    {X : Scheme.{0}} {x y : X ⟶ S} (h : x = y) :
    (1 : Over.mk x ⟶ G).left = (1 : Over.mk y ⟶ G).left := by
  subst h
  rfl

theorem UpperTheory.tangent_left_one :
    open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
        ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
          (v w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) ⟶ G),
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ w.left = (1 : Over.mk x ⟶ G).left →
            ∃ u : Spec (CommRingCat.of (TrivSqZeroExt R (R × R))) ⟶ G.left,
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R (R × R)).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom) ≫ u = v.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ≫ u = w.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom) ≫ u
                = (v * w).left := by
  open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
  · intro S G _ R _ x v w hv hw
    have hx : Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ x = x := by
      have : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := Spec.map_id _
      rw [this, Category.id_comp]
    have h1 := UpperTheory.grpObj_one_left_congr G hx
    have hv' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ v = 1 :=
      Over.OverMorphism.ext (hv.trans h1.symm)
    have hw' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ w = 1 :=
      Over.OverMorphism.ext (hw.trans h1.symm)
    have e0 : (TrivSqZeroExt.map (0 : R →ₗ[R] R)) =
        (Algebra.ofId R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R) := by
      apply AlgHom.ext
      intro a
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hv0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ v = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hv', MonObj.comp_one]
    have hw0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ w = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hw', MonObj.comp_one]
    let U : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R (R × R)))) ≫ x) ⟶ G :=
      (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inl R R R)) ≫ v) *
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inr R R R)) ≫ w)
    have key : ∀ f : (R × R) →ₗ[R] R, UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map f) ≫ U =
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inl R R R)) ≫ v) *
          (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inr R R R)) ≫ w) := by
      intro f
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.map_comp_map]
    have k0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R (R × R)) ≫ U = 1 := by
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.fstHom_comp_map]
      rw [hv', hw', _root_.mul_one]
    have k1 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R)) ≫ U = v := by
      rw [key, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hw0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.mul_one]
    have k2 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.snd R R R)) ≫ U = w := by
      rw [key, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hv0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.one_mul]
    have k3 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)) ≫ U
        = v * w := by
      rw [key, LinearMap.add_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, add_zero, zero_add,
        TrivSqZeroExt.map_id, UpperTheory.specMap_id, Category.id_comp, Category.id_comp]
    exact ⟨U.left, (congrArg CommaMorphism.left k0).trans h1, congrArg CommaMorphism.left k1,
      congrArg CommaMorphism.left k2, congrArg CommaMorphism.left k3⟩
end

namespace UpperTheory.Reformulated.B.Ga4

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

private structure ValueChart {X : Scheme.{0}} (G : Over X) [GrpObj G] (p : X) where
  B : CommRingCat.{0}
  al : X.presheaf.stalk p ⟶ B
  sg : B ⟶ X.presheaf.stalk p
  j : Spec B ⟶ G.left
  s : X ⟶ G.left
  n : ℕ
  d : B → Fin n → X.presheaf.stalk p
  one : ∀ {T : Scheme.{0}} (x : T ⟶ X), (1 : Over.mk x ⟶ G).left = x ≫ s
  mono : Mono j
  ovr : j ≫ G.hom = Spec.map al ≫ X.fromSpecStalk p
  sec : Spec.map sg ≫ j = X.fromSpecStalk p ≫ s
  fac : ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R)
    (v : Spec R' ⟶ G.left), Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
      Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ j
  surj : Function.Surjective d
  ex : ∀ (R : Type) [CommRing R] (φ : X.presheaf.stalk p →+* R) (c : Fin n → R), ∃ g : B →+* DualNumber R,
    (∀ a, g (al.hom a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (sg.hom b)) ∧
      ∀ b, (g b).snd = ∑ i, φ (d b i) * c i
  all : ∀ (R : Type) [CommRing R] (φ : X.presheaf.stalk p →+* R) (g : B →+* DualNumber R),
    (∀ a, g (al.hom a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (sg.hom b)) →
      ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i

private theorem chart_nonempty {X : Scheme.{0}} (G : Over X) [GrpObj G] [Smooth G.hom] (p : X) :
    Nonempty (ValueChart G p) := by
  let s : X ⟶ G.left := (η[G]).left
  have hs : s ≫ G.hom = 𝟙 X := Over.w (η[G])
  obtain ⟨B, al, sg, j, h1, h2, hm, ho, hsec, hfac⟩ := UpperTheory.formally_smooth_section_stalk G.hom s hs p
  have hid : al ≫ sg = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk p), Spec.map_comp, Category.assoc, ← ho, ← Category.assoc, hsec]
    simp [hs]
  obtain ⟨n, d, hd, hR⟩ := UpperTheory.formally_smooth_surjective_derivation al.hom sg.hom (congrArg CommRingCat.Hom.hom hid) h1 h2
  refine ⟨⟨B, al, sg, j, s, n, d, ?_, hm, ho, hsec, hfac, hd, fun R _ φ => (hR R φ).1, fun R _ φ => (hR R φ).2⟩⟩
  intro T x
  rw [Hom.one_def, Over.comp_left]
  simp [s]

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {p : X}

private def ValueChart.Rep (C : ValueChart G p) {R : Type} [CommRing R] (φ : X.presheaf.stalk p →+* R) (c : Fin C.n → R)
    (v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left) : Prop :=
  ∃ g : (C.B : Type) →+* DualNumber R,
    (∀ b : (↑C.B), TrivSqZeroExt.fst (R := R) (M := R) (g b) = φ (C.sg.hom b)) ∧
    (∀ b : (↑C.B), TrivSqZeroExt.snd (R := R) (M := R) (g b) = ∑ i, φ (C.d b i) * c i) ∧
      v = Spec.map (CommRingCat.ofHom (R := C.B) g) ≫ C.j

private theorem ValueChart.cancel (C : ValueChart G p) {R : CommRingCat.{0}} {g g' : C.B ⟶ R}
    (h : Spec.map g ≫ C.j = Spec.map g' ≫ C.j) : g = g' := by
  haveI := C.mono
  exact Spec.map_injective ((cancel_mono C.j).1 h)

variable {R : Type} [CommRing R]

private theorem ValueChart.rep_inj (C : ValueChart G p) {φ : X.presheaf.stalk p →+* R} {c c' : Fin C.n → R}
    {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) (h' : C.Rep φ c' v) : c = c' := by
  obtain ⟨g, -, h2, h3⟩ := h
  obtain ⟨g', -, h2', h3'⟩ := h'
  have hg : g = g' := congrArg CommRingCat.Hom.hom (C.cancel (h3.symm.trans h3'))
  subst hg
  funext i
  obtain ⟨b, hb⟩ := C.surj (Pi.single i 1)
  have := (h2 b).symm.trans (h2' b)
  simpa [hb, Pi.single_apply, apply_ite φ] using this

private theorem ValueChart.rep_uniq (C : ValueChart G p) {φ : X.presheaf.stalk p →+* R} {c : Fin C.n → R}
    {v v' : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) (h' : C.Rep φ c v') : v = v' := by
  obtain ⟨g, h1, h2, h3⟩ := h
  obtain ⟨g', h1', h2', h3'⟩ := h'
  have hg : g = g' := RingHom.ext fun b => TrivSqZeroExt.ext ((h1 b).trans (h1' b).symm) ((h2 b).trans (h2' b).symm)
  rw [h3, h3', hg]

private theorem ValueChart.rep_base (C : ValueChart G p) {R' : Type} [CommRing R'] (χ : R →+* R') {φ : X.presheaf.stalk p →+* R}
    {c : Fin C.n → R} {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) :
    C.Rep (χ.comp φ) (fun i => χ (c i)) (Spec.map (CommRingCat.ofHom (dualMap χ)) ≫ v) := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨(dualMap χ).comp g, fun b => ?_, fun b => ?_, ?_⟩
  · simp [dualMap, h1]
  · simp [dualMap, h2]
  · rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem ValueChart.rep_smul (C : ValueChart G p) (r : R) {φ : X.presheaf.stalk p →+* R}
    {c : Fin C.n → R} {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) :
    C.Rep φ (r • c) (Spec.map (CommRingCat.ofHom (epsMul r)) ≫ v) := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨(epsMul r).comp g, fun b => ?_, fun b => ?_, ?_⟩
  · simp [epsMul, h1]
  · simp [epsMul, h2, Finset.mul_sum, mul_left_comm]
  · rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem ValueChart.rep_exists (C : ValueChart G p) (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (c : Fin C.n → R) :
    ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ C.Rep φ.hom c v.left := by
  obtain ⟨g, h0, h1, h2⟩ := C.ex R φ.hom c
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom g) ≫ C.j) ?_, ?_, g, h1, h2, rfl⟩
  · have : C.al ≫ CommRingCat.ofHom g =
        φ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
      ext1; ext1 a; exact h0 a
    change (Spec.map (CommRingCat.ofHom g) ≫ C.j) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x
    rw [Category.assoc, C.ovr, ← Category.assoc, ← Spec.map_comp, this, hx, Spec.map_comp, Category.assoc]
  · have : CommRingCat.ofHom g ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom =
        C.sg ≫ φ := by
      ext1; ext1 b; exact h1 b
    unfold IsTanAt
    rw [C.one]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom g) ≫ C.j = _
    rw [← Category.assoc, ← Spec.map_comp, this, Spec.map_comp, Category.assoc, C.sec, hx, Category.assoc]

private theorem ValueChart.fac' (C : ValueChart G p) [IsLocalRing R] {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p)
    (u : Spec (CommRingCat.of (TrivSqZeroExt R N)) ⟶ G.left)
    (hu : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R N).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left) :
    ∃ g : (C.B : Type) →+* TrivSqZeroExt R N,
      (∀ b : (↑C.B), TrivSqZeroExt.fst (R := R) (M := N) (g b) = φ.hom (C.sg.hom b)) ∧
      u = Spec.map (CommRingCat.ofHom (R := C.B) g) ≫ C.j := by
  rw [C.one, hx, Category.assoc] at hu
  obtain ⟨g, hg⟩ := C.fac (CommRingCat.of R) (CommRingCat.of (TrivSqZeroExt R N)) _ φ u
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun y hy => by
      have hy' : y.fst = 0 := hy
      ext <;> simp [hy']) hu
  refine ⟨g.hom, fun b => ?_, hg⟩
  rw [hg, ← C.sec, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at hu
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (C.cancel hu)

private theorem ValueChart.rep_of_tan (C : ValueChart G p) [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    ∃ c : Fin C.n → R, C.Rep φ.hom c v.left := by
  obtain ⟨g, h1, hg⟩ := C.fac' φ x hx v.left hv
  have hw : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := Over.w v
  rw [hg, Category.assoc, C.ovr, hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    cancel_mono] at hw
  have h0 := Spec.map_injective hw
  obtain ⟨c, hc⟩ := C.all R φ.hom g (fun a => congrArg (fun k => CommRingCat.Hom.hom k a) h0) h1
  exact ⟨c, g, h1, hc, hg⟩

private theorem ValueChart.rep_mul (C : ValueChart G p) [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (v w : epsAt x ⟶ G) (hv : IsTanAt G x v)
    (hw : IsTanAt G x w) {c c' : Fin C.n → R} (h : C.Rep φ.hom c v.left) (h' : C.Rep φ.hom c' w.left) :
    C.Rep φ.hom (c + c') (v * w).left := by
  obtain ⟨u, u0, u1, u2, u3⟩ := UpperTheory.tangent_left_one G x v w hv hw
  obtain ⟨k, hk, hu⟩ := C.fac' φ x hx u u0
  obtain ⟨g, -, h2, h3⟩ := h
  obtain ⟨g', -, h2', h3'⟩ := h'
  rw [hu, h3, ← Category.assoc, ← Spec.map_comp] at u1
  rw [hu, h3', ← Category.assoc, ← Spec.map_comp] at u2
  have e1 : ∀ b, (k b).snd.1 = (g b).snd := fun b => by
    have := congrArg (fun k : C.B ⟶ CommRingCat.of (DualNumber R) =>
      TrivSqZeroExt.snd (R := R) (M := R) (k.hom b)) (C.cancel u1)
    simpa using this
  have e2 : ∀ b, (k b).snd.2 = (g' b).snd := fun b => by
    have := congrArg (fun k : C.B ⟶ CommRingCat.of (DualNumber R) =>
      TrivSqZeroExt.snd (R := R) (M := R) (k.hom b)) (C.cancel u2)
    simpa using this
  refine ⟨(TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom.comp k, fun b => ?_,
    fun b => ?_, ?_⟩
  · simp [hk]
  · simp [e1, e2, h2, h2', mul_add, Finset.sum_add_distrib]
  · rw [← u3, hu, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem ValueChart.coords (C : ValueChart G p) [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : ∃ κ : E ≃ₗ[R] (Fin C.n → R), ∀ e : E, C.Rep φ.hom (κ e) (M.pt e).left := by
  choose f hf using fun e => C.rep_of_tan φ x hx (M.pt e) (M.tan e)
  let l : E →ₗ[R] (Fin C.n → R) :=
    { toFun := f
      map_add' := fun e e' => C.rep_inj (hf _) (by
        rw [M.add]; exact C.rep_mul φ x hx _ _ (M.tan e) (M.tan e') (hf e) (hf e'))
      map_smul' := fun r e => C.rep_inj (hf _) (by
        rw [M.smul]; exact C.rep_smul r (hf e)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun e e' h => ?_, fun c => ?_⟩, hf⟩
  · have h' : f e = f e' := h
    exact M.inj (Over.OverMorphism.ext (C.rep_uniq (hf e) (h' ▸ hf e')))
  · obtain ⟨v, hv, hc⟩ := C.rep_exists φ x hx c
    obtain ⟨e, rfl⟩ := M.onto v hv
    exact ⟨e, C.rep_inj (hf e) hc⟩

private theorem ValueChart.rep_val (C : ValueChart G p) (χ : X.presheaf.stalk p ⟶ CommRingCat.of R) {a : Fin C.n → X.presheaf.stalk p}
    {v : Spec (CommRingCat.of (DualNumber (X.presheaf.stalk p))) ⟶ G.left}
    (h : C.Rep (R := X.presheaf.stalk p) (CommRingCat.Hom.hom (𝟙 (X.presheaf.stalk p))) a v) :
    C.Rep χ.hom (fun i => χ.hom (a i)) (Spec.map (CommRingCat.ofHom (dualMap χ.hom)) ≫ v) :=
  C.rep_base χ.hom h

private theorem gen_fac {x : X} (h : x ⤳ p) {S : CommRingCat.{0}} (k : X.presheaf.stalk x ⟶ S) :
    Spec.map (X.presheaf.stalkSpecializes h ≫ k) ≫ X.fromSpecStalk p = Spec.map k ≫ X.fromSpecStalk x := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end UpperTheory.Reformulated.B.Ga4

theorem UpperTheory.Reformulated.B.Ga4.exists_value_basis :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
    {ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X} {G : CategoryTheory.Over X} [inst_1 : CategoryTheory.GrpObj G]
    {Li : Type} [inst_2 : AddCommGroup Li] [inst_3 : _root_.Module Ω Li] [CategoryTheory.IsCommMonObj G]
    [AlgebraicGeometry.Smooth G.hom],
    GlobalTheory.CompanionTheory.Ar.IsCptGen ξ →
      ∀ (M : GlobalTheory.CompanionTheory.Ar.LieModel G ξ Li) (z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
        (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {V I : Type} [inst_6 : AddCommGroup V] [inst_7 : _root_.Module ℂ V]
        (Mz : GlobalTheory.CompanionTheory.Ar.LieModel G z V) [Fintype I] (F : I → Li),
        LinearIndependent Ω F →
          M.lat ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ = Submodule.span (↥(GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩)) (Set.range F) →
            ∃ (y : Module.Basis I ℂ V),
              ∀ (j : I),
                M.ValAt z (F j)
                  (Mz.pt
                    ((y : I → V)
                      j)) := by
  open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar in
  intro X Ω _ ξ G _ Li _ _ _ _ hξ M z h V I _ _ Mz _ F hF hL
  obtain ⟨C⟩ := chart_nonempty G (centre z)
  let φ : X.presheaf.stalk (centre z) ⟶ CommRingCat.of Ω :=
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ
  let ψ : X.presheaf.stalk (centre z) ⟶ CommRingCat.of ℂ := Scheme.stalkClosedPointTo z
  have hφ : ξ = Spec.map φ ≫ X.fromSpecStalk (centre z) :=
    ((gen_fac h (Scheme.stalkClosedPointTo ξ)).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)).symm
  have hψ : z = Spec.map ψ ≫ X.fromSpecStalk (centre z) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm
  have hi : X.fromSpecStalk (centre z) = Spec.map (𝟙 (X.presheaf.stalk (centre z))) ≫
      X.fromSpecStalk (centre z) := by
    rw [Spec.map_id, Category.id_comp]
  obtain ⟨κ, hκ⟩ := C.coords φ ξ hφ M
  obtain ⟨κ', hκ'⟩ := C.coords ψ z hψ Mz
  have hext : ∀ (e : Li) (a : Fin C.n → X.presheaf.stalk (centre z)), (κ e = fun i => φ.hom (a i)) →
      ∃ v, M.Extends ⟨centre z, h⟩ e v ∧
        C.Rep (R := X.presheaf.stalk (centre z)) (CommRingCat.Hom.hom (𝟙 (X.presheaf.stalk (centre z)))) a v.left := by
    intro e a ha
    obtain ⟨v, hv, hr⟩ := C.rep_exists (R := X.presheaf.stalk (centre z)) (𝟙 (X.presheaf.stalk (centre z)))
      (X.fromSpecStalk (centre z)) hi a
    have h1 := hκ e
    rw [ha] at h1
    exact ⟨v, ⟨hv, C.rep_uniq h1 (C.rep_val φ hr)⟩, hr⟩
  have hset : {e : Li | ∃ a : Fin C.n → X.presheaf.stalk (centre z), κ e = fun i => φ.hom (a i)} =
      {e | ∃ v, M.Extends ⟨centre z, h⟩ e v} := by
    ext e
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨v, hv, -⟩ := hext e a ha
      exact ⟨v, hv⟩
    · rintro ⟨v, hv, he⟩
      obtain ⟨a, ha⟩ := @ValueChart.rep_of_tan _ _ _ _ (X.presheaf.stalk (centre z)) _ C
        (X.toLocallyRingedSpace.isLocalRing (centre z)) (𝟙 (X.presheaf.stalk (centre z)))
        (X.fromSpecStalk (centre z)) hi v hv
      have h1 := hκ e
      rw [he] at h1
      exact ⟨a, C.rep_inj h1 (C.rep_val φ ha)⟩
  obtain ⟨y, hy⟩ := UpperTheory.span_linear_independent_base φ.hom ψ.hom κ κ' F (hξ.inj ⟨centre z, h⟩) hF (by rw [hset]; exact hL)
  refine ⟨y, fun j => ?_⟩
  obtain ⟨a, ha, ha'⟩ := hy j
  obtain ⟨v, hv, hr⟩ := hext (F j) a ha
  have h1 := hκ' (y j)
  rw [ha'] at h1
  exact ⟨h, v, hv, C.rep_uniq h1 (C.rep_val ψ hr)⟩
