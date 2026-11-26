module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatClosedSubschemeFiniteOverLocalRingStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatClosedSubschemeFiniteOverLocalRing
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.StabFlat

theorem eq_ker_stalkMap_of_points {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (h : H)
    (I : Ideal (X.presheaf.stalk (j h)))
    (hI : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔
        I ≤ RingHom.ker φ) : I = RingHom.ker (j.stalkMap h).hom := by
  have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
    (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
      ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
  have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
  have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : y (IsLocalRing.closedPoint _) = h := by
    apply j.isClosedEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
    exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
  have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
  refine le_antisymm h₁ fun a ha => Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [← hψ', RingHom.mem_ker.1 ha, map_zero]

theorem flat_of_isFinite_of_ideals : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ X H f j hj hfin hI
  refine Flat.of_stalkMap _ fun h' => ?_
  obtain ⟨h, hh, hc⟩ : ∃ h : H, h' ⤳ h ∧ (j ≫ f) h = IsLocalRing.closedPoint V := by
    have hcl : IsClosed ((j ≫ f) '' closure {h'}) := (j ≫ f).isClosedMap _ isClosed_closure
    have hm : IsLocalRing.closedPoint V ∈ (j ≫ f) '' closure {h'} :=
      (IsLocalRing.specializes_closedPoint ((j ≫ f) h')).mem_closed hcl ⟨h', subset_closure rfl, rfl⟩
    obtain ⟨h, hh, e⟩ := hm
    exact ⟨h, specializes_iff_mem_closure.2 hh, e⟩
  refine UnramifiedEndFlat.flat_stalkMap_of_specializes _ hh ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have hloc : IsLocalHom σ.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint σ.hom).2 ?_
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ).trans ?_
    exact (congrArg f Scheme.fromSpecStalk_closedPoint).trans hc
  obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hloc
  obtain rfl := eq_ker_stalkMap_of_points j h I hI
  have fl : (σ ≫ j.stalkMap h).hom.Flat :=
    hr.comp (RingHom.Flat.of_bijective
      (f := (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).toRingHom)
      (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective h)).bijective)
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl

end GlobalTheory.StabFlat
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_closedSubscheme_finite_over_localRing : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  first | exact @GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | exact GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | (intros; apply GlobalTheory.StabFlat.flat_of_isFinite_of_ideals <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatQuotientOfEquivCokerDualMapOfExactFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfComplexExactModMaximalIdeal
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

theorem flat_coker_of_complex_exact_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by
  intro V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex
  set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ
  have hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0) := by
    rintro _ ⟨x, rfl⟩
    exact hdd 0 x
  let u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0 := (LinearMap.range (d 1)).liftQ (d 0) hle
  have hr : LinearMap.range u = LinearMap.range (d 0) := Submodule.range_liftQ _ _ _
  have h := GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1)) := hex 0 y hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [Submodule.Quotient.mk_add, ha0, zero_add]
    have : (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ :=
      Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this)
  rwa [hr] at h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatQuotientOfEquivCokerDualMapOfExactFibres
open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory
namespace DualCokernelFlat

section Modules

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem dual_baseChange_surjective (hs : Surjective (algebraMap A B)) (M : Type) [AddCommGroup M]
    [Module A M] [Module.Projective A M] :
    Surjective (Module.Dual.baseChange B : Module.Dual A M → Module.Dual B (B ⊗[A] M)) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A B)
    (g.restrictScalars A ∘ₗ TensorProduct.mk A B M 1) hs
  refine ⟨f, ?_⟩
  ext x
  have := LinearMap.congr_fun hf x
  simpa [Algebra.algebraMap_eq_smul_one] using this

theorem dual_baseChange_eq_zero_iff (M : Type) [AddCommGroup M]
    [Module A M] [Module.Free A M] [Module.Finite A M] (f : Module.Dual A M) :
    Module.Dual.baseChange B f = 0 ↔
      f ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M)) := by
  constructor
  · intro h
    let b := Module.Free.chooseBasis A M
    rw [← b.sum_dual_apply_smul_coord f]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have := LinearMap.congr_fun h (1 ⊗ₜ b i)
    simpa [RingHom.mem_ker, Algebra.algebraMap_eq_smul_one] using this
  · intro h
    refine Submodule.smul_induction_on h (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, ← algebraMap_smul B r, RingHom.mem_ker.mp hr, zero_smul]
    · rw [map_add (f := _), hx, hy, add_zero]

theorem dual_baseChange_dualMap {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (a : M →ₗ[A] N) (f : Module.Dual A N) :
    Module.Dual.baseChange B (a.dualMap f) =
      (a.baseChange B).dualMap (Module.Dual.baseChange B f) := by
  ext x
  simp

theorem mem_sup_of_exact (hs : Surjective (algebraMap A B)) {M₀ M₁ M₂ : Type}
    [AddCommGroup M₀] [Module A M₀] [Module.Free A M₀] [Module.Finite A M₀]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] (a : M₀ →ₗ[A] M₁) (b : M₁ →ₗ[A] M₂)
    (h : Exact (b.baseChange B).dualMap (a.baseChange B).dualMap) (x : Module.Dual A M₁)
    (hx : a.dualMap x ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₀))) :
    x ∈ LinearMap.range b.dualMap ⊔
      (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₁)) := by
  rw [← dual_baseChange_eq_zero_iff, dual_baseChange_dualMap] at hx
  obtain ⟨y, hy⟩ := (h _).1 hx
  obtain ⟨y, rfl⟩ := dual_baseChange_surjective hs M₂ y
  have : x = b.dualMap y + (x - b.dualMap y) := by abel
  rw [this]
  refine Submodule.add_mem_sup ⟨y, rfl⟩ ?_
  rw [← dual_baseChange_eq_zero_iff, map_sub, dual_baseChange_dualMap, hy, sub_self]

end Modules

theorem mem_sup_of_exact_fibres {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (π : A →+* B) (hs : Surjective π) (g : ℕ) (hg : ringKrullDim B = g)
    (C : CochainComplex (ModuleCat.{0} A) ℕ)
    (hF : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hn : ∃ n, ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : PrimeSpectrum A, RingHom.ker π ≤ p.asIdeal → ∃ (K : Type) (_ : Field K)
      (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
        ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i)
    (i : ℕ) (x : Module.Dual A (C.X (i + 1)))
    (hx : (C.d i (i + 1)).hom.dualMap x ∈
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X i)))) :
    x ∈ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ⊔
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X (i + 1)))) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let := π.toAlgebra
  have key := GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing B g hg (((ModuleCat.extendScalars π).mapHomologicalComplex _).obj C)
    (fun i => ⟨inferInstanceAs (Module.Free B (B ⊗[A] C.X i)),
      inferInstanceAs (Module.Finite B (B ⊗[A] C.X i))⟩)
    (hn.imp fun n h i hi => (ModuleCat.extendScalars π).map_isZero (h i hi)) (fun q => ?_) i
  · exact mem_sup_of_exact (B := B) hs _ _ key x hx
  obtain ⟨K, _, φ, hφ, hK⟩ := hex (q.comap π) (by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le)
  have hle : RingHom.ker π ≤ RingHom.ker φ := by
    rw [hφ, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  obtain ⟨ψ, rfl⟩ : ∃ ψ : B →+* K, ψ.comp π = φ :=
    ⟨π.liftOfSurjective hs ⟨φ, hle⟩, π.liftOfSurjective_comp hs _⟩
  refine ⟨K, inferInstance, ψ, ?_, fun j hj => ?_⟩
  · apply Ideal.comap_injective_of_surjective π hs
    rw [RingHom.comap_ker, hφ]
    rfl
  · refine (hK j (hj.imp_left fun h h' => h ?_)).of_iso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp π ψ) _).app C)
    have hm : (q.asIdeal.comap π).IsMaximal := by
      have : q.asIdeal.comap π = IsLocalRing.maximalIdeal A := h'
      rw [this]
      infer_instance
    have := (Ideal.comap_isMaximal_of_surjective π hs (K := IsLocalRing.maximalIdeal B))
    apply Ideal.comap_injective_of_surjective π hs
    rw [IsLocalRing.eq_maximalIdeal hm, IsLocalRing.eq_maximalIdeal this]

end DualCokernelFlat


open DualCokernelFlat in
theorem flat_quotient_of_equiv_coker_dualMap_of_exact_fibres :
    ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A]
      [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)]
      [Module.Flat V A] (g : ℕ),
      IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) →
      ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal →
        ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
          ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸
        LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  intro V A _ _ _ _ _ _ _ _ _ g hreg hg C hF hn hex I ⟨e⟩
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hflat : ∀ i, Module.Flat V (Module.Dual A (C.X i)) := fun i => Module.Flat.trans V A _
  have key := mem_sup_of_exact_fibres (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective g hg C hF
    hn (by rw [Ideal.mk_ker]; exact hex)
  rw [Ideal.mk_ker] at key
  have h := GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal V A (fun i => Module.Dual A (C.X i))
    (fun i => (C.d i (i + 1)).hom.dualMap) (fun i f => ?_) (hn.imp fun n h i hi => ?_) key
  · exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm
  · ext x
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← LinearMap.comp_apply (C.d _ _).hom,
      ← ModuleCat.hom_comp, C.d_comp_d]
    simp
  · have := ModuleCat.subsingleton_of_isZero (h i hi)
    infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatQuotientOfEquivCokerDualMapOfExactFibresStatement
open CategoryTheory CategoryTheory.Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres_alt : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (g : ℕ), IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) → ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  first | exact @GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres | exact GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres | (intros; apply GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.StabFlatLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat

theorem exists_ideal (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (σ : V →+* A) (hσ : IsLocalHom σ) (h₁ : σ.Flat)
    (h₂ : IsRegularLocalRing (A ⧸ (IsLocalRing.maximalIdeal V).map σ))
    (h₃ : ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal V).map σ) = g)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a)
    (hE : ∀ (K : Type) [Field K] (φ : A →+* K), (IsLocalRing.maximalIdeal V).map σ ≤ RingHom.ker φ →
      (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
      RingHom.ker φ = IsLocalRing.maximalIdeal A) :
    ∃ I : Ideal A, ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
        I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, ?_, fun R _ _ φ => (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans
    (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  letI : Algebra V A := σ.toAlgebra
  haveI : IsLocalHom (algebraMap V A) := hσ
  haveI : Module.Flat V A := h₁
  have key : Module.Flat V (A ⧸ I) → ((Ideal.Quotient.mk I).comp σ).Flat := fun h =>
    RingHom.flat_algebraMap_iff.2 h
  refine key (GlobalTheory.T.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres_alt V A g h₂ h₃ C c₁ c₂ (fun p hϖ => ?_) I ⟨eC.trans eI⟩)
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let φ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  have hk : RingHom.ker φ = p.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · refine Or.inr fun ht => hi (hk.symm.trans (hE K φ ?_ ((test K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)))
    exact hϖ.trans hk.ge
  · exact Or.inl hi

theorem flat_of_isFinite : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ H j hj hH hf
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L (pw L 0) hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x))
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.StabFlatLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  first | exact @GlobalTheory.StabFlatLocal.flat_of_isFinite | exact GlobalTheory.StabFlatLocal.flat_of_isFinite | (intros; apply GlobalTheory.StabFlatLocal.flat_of_isFinite <;> assumption)
end
