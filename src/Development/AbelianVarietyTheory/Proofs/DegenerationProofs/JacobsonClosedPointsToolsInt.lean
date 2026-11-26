module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoGenericOfDenseFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory

theorem jacobson_closedPoints_tools_int : ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧ (∀ (ξ : X) (κ : Type) [Finite κ] (U : κ → X.Opens) (W : X.Opens), ξ ∈ W → ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧ (∀ (κ : Type) [Finite κ] (Sg : κ → Set X), IrreducibleSpace X → (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) :=
  jacobson_tools_of_locallyOfFiniteType_int
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem henselianLocalRing_valuationSubring_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : HenselianLocalRing V where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hg : (f.map (algebraMap V K)).Monic := hf.map _
    have hsplit : (f.map (algebraMap V K)).Splits := IsAlgClosed.splits _

    have hev : ((f.eval a₀ : V) : K) =
        ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod := by
      have h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm
      rw [h1]
      exact hsplit.eval_eq_prod_roots_of_monic hg _
    have hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1 := by
      rw [← hev]
      exact (ValuationSubring.valuation_lt_one_iff V _).mp h₁
    rw [map_multiset_prod, Multiset.map_map] at hlt

    obtain ⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by
      by_contra hcon
      push Not at hcon
      refine absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))
      simp only [Multiset.mem_map, Function.comp_apply]
      rintro _ ⟨s, hs, rfl⟩
      exact hcon s hs
    have hrV : r ∈ V := by
      rw [← V.valuation_le_one_iff]
      have h2 : r = (a₀ : K) - ((a₀ : K) - r) := by ring
      rw [h2]
      exact (Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)
    refine ⟨⟨r, hrV⟩, ?_, ?_⟩
    · have hroot := (Polynomial.mem_roots hg.ne_zero).mp hr
      show Polynomial.eval _ f = 0
      apply Subtype.ext
      have h3 := Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)
      rw [← Polynomial.eval_map] at h3
      simpa using h3.symm.trans hroot
    · rw [ValuationSubring.valuation_lt_one_iff]
      have h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀ := rfl
      rw [h4, Valuation.map_sub_swap]
      exact hrlt

theorem ZJ.exists_classical_lift_of_smooth :
    ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  intro p _ X S f _ y x hx
  have : HenselianLocalRing (OO p) := henselianLocalRing_valuationSubring_of_isAlgClosed _
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩
  exact ⟨b, hb, congrArg Subtype.val hb'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct

namespace GlobalTheory

namespace GenericEq

open GenericIso

theorem map_eq_generic (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)) (hD : Dense Sg)
    (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y)
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (Over.pullback t).map f = (Over.pullback t).map g) :
    (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g := by
  have : IsClosedImmersion (equalizer.ι f g).left := inferInstance
  have : LocallyOfFiniteType (equalizer f g).hom := by
    rw [← Over.w (equalizer.ι f g)]; infer_instance
  have h := isIso_generic_of_dense_fibres R (equalizer f g) X (equalizer.ι f g) Sg hD
    fun x hx => by
      obtain ⟨K, _, t, ht, e⟩ := H x hx
      refine ⟨K, inferInstance, t, ht, ?_⟩
      rw [← equalizerComparison_comp_π]
      have := equalizer.ι_of_eq e
      infer_instance
  rw [← cancel_epi ((Over.pullback (Out.jK R)).map (equalizer.ι f g)), ← Functor.map_comp,
    ← Functor.map_comp, equalizer.condition]

theorem exists_smul_eq_zero {R A : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (y : A) (H : ∀ x ∈ D, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
      x.asIdeal = RingHom.ker (algebraMap R K) ∧ (1 : K) ⊗ₜ[R] y = 0) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R A a * y = 0 := by
  let F := Ideal.Quotient.mkₐ R (Ideal.span {y})
  have hF : Function.Surjective F := Ideal.Quotient.mkₐ_surjective _ _
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense F hD fun x hx => by
    obtain ⟨K, _, _, hK, hy⟩ := H x hx
    refine (bijective_residueField F K x hK ⟨?_,
      Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hF⟩).1
    rw [RingHom.injective_iff_ker_eq_bot, Algebra.TensorProduct.lTensor_ker F hF,
      show RingHom.ker F = Ideal.span {y} from Ideal.mk_ker,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact hy
  obtain ⟨n, hn⟩ := ha y (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self y))
  exact ⟨a ^ n, pow_ne_zero _ ha0, by rw [← Algebra.smul_def]; exact hn⟩

theorem appTop_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Z ⟶ Y) (p : Y ⟶ Sp R)
    (a : R) : q.appTop.hom (Out.scal p a) = Out.scal (q ≫ p) a := by
  rfl

theorem exists_scal_mul_chart {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] {Sg : Set (Sp R)} (hD : Dense Sg)
    (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0)
    (A : CommRingCat.{0}) (j : Spec A ⟶ X.left) [IsOpenImmersion j] :
    ∃ a : R, a ≠ 0 ∧ j.appTop.hom (Out.scal X.hom a * u) = 0 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ X.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ X.hom := hφ
  obtain ⟨a, ha0, ha⟩ := exists_smul_eq_zero (R := R) hD
    ((Scheme.ΓSpecIso A).hom.hom (j.appTop.hom u)) fun x hx => by
      obtain ⟨K, _, t, ht, hu⟩ := H x hx
      obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
      let : Algebra R K := ψ.hom.toAlgebra
      refine ⟨K, inferInstance, inferInstance, ?_, ?_⟩
      · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
          ht.le (Set.mem_range_self _)
        rw [← this]
        rfl
      · have w := (isPullback_tensor (R := R) K A).w
        rw [hφ', ← Category.assoc] at w
        have e := congrArg (fun k => k.appTop.hom u) (pullback.lift_fst _ _ w)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        erw [hu, map_zero] at e
        have n := congrArg (fun k => k.hom (j.appTop.hom u)) (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := A)).toRingHom))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
        erw [← e, map_zero] at n
        exact n.symm
  refine ⟨a, ha0, ?_⟩
  apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← ha, map_mul, map_mul, appTop_scal, ← hφ]
  congr 1
  have n := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
  refine n.trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_scal_mul_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0) :
    ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0 := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have hc : ∀ i : 𝒰.I₀, ∃ a : R, a ≠ 0 ∧ (𝒰.f i).appTop.hom (Out.scal X.hom a * u) = 0 := by
    intro i
    obtain ⟨a, ha0, ha⟩ :=
      exists_scal_mul_chart X hD u H _ ((𝒰.X i).isoSpec.inv ≫ 𝒰.f i)
    refine ⟨a, ha0, ?_⟩
    rw [← (𝒰.X i).isoSpec.hom_inv_id_assoc (𝒰.f i), Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
  choose a ha0 ha using hc
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i,
    Scheme.zero_of_zero_cover _ 𝒰 fun i => ?_⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have e : Out.scal X.hom (∏ i, a i) * u = Out.scal X.hom b * (Out.scal X.hom (a i) * u) := by
    rw [hb]
    simp only [Out.scal, map_mul]
    ring
  rw [e, map_mul]
  exact mul_eq_zero_of_right _ (ha i)

theorem exists_mem_of_not_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (V : X.left.Opens) (H : ∀ x : X.left, X.hom x ∈ Sg → x ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hC : Topology.IsConstructible ((V : Set X.left)ᶜ) :=
    (IsCompact.isConstructible (TopologicalSpace.NoetherianSpace.isCompact _) V.isOpen).compl
  obtain ⟨W, ⟨y, hy⟩, -, hW⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense X.left (Sp R) X.hom
      _ Sg hC hD (Set.disjoint_left.2 (by rintro _ ⟨x, hx, rfl⟩ h; exact hx (H x h)))
  obtain ⟨_, ⟨a, rfl⟩, hya, haW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.isOpen
  refine ⟨a, ?_, fun x hx => ?_⟩
  · rintro rfl
    exact hya (Ideal.zero_mem _)
  · by_contra hxV
    exact Set.disjoint_left.1 hW ⟨x, hxV, rfl⟩ (haW hx)

end GenericEq

open GenericEq

theorem generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)), Dense Sg → (∀ (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (Over.pullback t).map f = (Over.pullback t).map g) → (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g) ∧ (∀ u : Γ(X.left, ⊤), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (pullback.fst X.hom t).appTop.hom u = 0) → ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0) ∧ (∀ V : X.left.Opens, (∀ x : X.left, X.hom x ∈ Sg → x ∈ V) → ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V) := by
  intro R _ _ _ X _ _ Sg hD
  exact ⟨fun Y _ f g => map_eq_generic R X Sg hD Y f g, exists_scal_mul_eq_zero R X Sg hD,
    exists_mem_of_not_mem R X Sg hD⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericConnected

theorem exists_spread {X Y S : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (j : Spec (.of R) ⟶ S) {p : X ⟶ S} [QuasiCompact p]
    [LocallyOfFiniteType p] {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j))
    (U V : Y.Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    ∃ (T : Scheme.{0}) (a : T ⟶ Spec (.of R)) (_ : LocallyOfFiniteType a) (_ : IsAffine T)
      (b : Spec (.of A) ⟶ T) (π : Y ⟶ pullback p (a ≫ j)) (U' V' : (pullback p (a ≫ j)).Opens),
      b ≫ a = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      π ≫ pullback.snd p (a ≫ j) = q ≫ b ∧
      U' ⊔ V' = ⊤ ∧ U' ⊓ V' = ⊥ ∧ π ⁻¹ᵁ U' = U ∧ π ⁻¹ᵁ V' = V := by
  classical
  let F : Finset A ⥤ CommRingCat.{0} :=
    { obj s := .of (Algebra.adjoin R (s : Set A))
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of A
      «ι» := { app s := CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin R (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset A)ᵒᵖ ⥤ Scheme.{0} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let a (s : (Finset A)ᵒᵖ) : G.obj s ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
  have ha {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ a t = a s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have ha' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ a s = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let e (s : (Finset A)ᵒᵖ) : G.obj s ⟶ S := a s ≫ j
  have hι {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ e t = e s := by
    change G.map f ≫ a t ≫ j = a s ≫ j
    rw [← Category.assoc, ha]
  have hι' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ e s = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j := by
    change cG.π.app s ≫ a s ≫ j = _
    rw [← Category.assoc, ha']
  let D : (Finset A)ᵒᵖ ⥤ Scheme.{0} :=
    { obj s := pullback p (e s)
      map {s t} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ G.map f)
        (by rw [Category.assoc, hι, pullback.condition])
      map_id s := by apply pullback.hom_ext <;> simp
      map_comp f f' := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            G.map_comp, Category.assoc] }
  let α : D ⟶ G :=
    { app s := pullback.snd p (e s)
      naturality s t f := pullback.lift_snd _ _ _ }
  let π (s : (Finset A)ᵒᵖ) : Y ⟶ pullback p (e s) :=
    pullback.lift g (q ≫ cG.π.app s) (by rw [Category.assoc, hι', H.w])
  let cD : Cone D :=
    { pt := Y
      π :=
        { app := π
          naturality s t f := by
            change 𝟙 Y ≫ π t = π s ≫ pullback.lift _ _ _
            apply pullback.hom_ext
            · rw [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst,
                pullback.lift_fst]
            · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd,
                pullback.lift_snd_assoc, Category.assoc, cG.w f] } }
  have hπ (s : (Finset A)ᵒᵖ) : IsPullback (π s) q (pullback.snd p (e s)) (cG.π.app s) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (e s)) (v₁₃ := p) (h₂₂ := e s) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [hι', pullback.lift_fst]
    exact H
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := q, w s := (pullback.lift_snd _ _ _).symm } hπ hcG
  have hG (s : (Finset A)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f) := by
    have : IsPullback (D.map f) (pullback.snd p (e s)) (pullback.snd p (e t)) (G.map f) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst p (e t)) (v₁₃ := p) (h₂₂ := e t) ?_
        (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
      rw [hι, pullback.lift_fst]
      exact .of_hasPullback _ _
    exact MorphismProperty.of_isPullback this.flip inferInstance
  have hcpt (s : (Finset A)ᵒᵖ) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (e s))
  have hft (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (a s) := by
    have : Algebra.FiniteType R (Algebra.adjoin R (s.unop : Set A)) :=
      Algebra.FiniteType.adjoin_of_finite s.unop.finite_toSet
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)
  have hnoeth (s : (Finset A)ᵒᵖ) : TopologicalSpace.NoetherianSpace (D.obj s) := by
    have : IsLocallyNoetherian (D.obj s) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (e s) ≫ a s)
    have : IsNoetherian (D.obj s) := {}
    infer_instance
  have hw {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) (W : (D.obj t).Opens) :
      cD.π.app s ⁻¹ᵁ D.map f ⁻¹ᵁ W = cD.π.app t ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, cD.w]
  have : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have hsup' : (U : Set Y) ∪ V = Set.univ := by simpa using congr(($hsup : Set Y))
  have hinf' : (U : Set Y) ∩ V = ∅ := by simpa using congr(($hinf : Set Y))
  have hUV : IsCompl (U : Set Y) V := ⟨Set.disjoint_iff_inter_eq_empty.2 hinf', codisjoint_iff.2 hsup'⟩
  have hUc : IsCompact (U : Set Y) := by
    rw [hUV.eq_compl]; exact V.2.isClosed_compl.isCompact
  have hVc : IsCompact (V : Set Y) := by
    rw [hUV.symm.eq_compl]; exact U.2.isClosed_compl.isCompact
  obtain ⟨i₁, U₁, -, hU₁⟩ := exists_preimage_eq D cD hcD U hUc
  obtain ⟨i₂, V₁, -, hV₁⟩ := exists_preimage_eq D cD hcD V hVc
  let f₁ := IsCofiltered.minToLeft i₁ i₂
  let f₂ := IsCofiltered.minToRight i₁ i₂
  obtain ⟨i₃, f₃, h₃⟩ := exists_map_eq_top D cD hcD (D.map f₁ ⁻¹ᵁ U₁ ⊔ D.map f₂ ⁻¹ᵁ V₁) (by
    rw [Scheme.Hom.preimage_sup, hw, hw, hU₁, hV₁]; exact hsup)
  obtain ⟨i₄, f₄, h₄⟩ := exists_map_preimage_le_map_preimage D cD hcD
    (U := D.map f₃ ⁻¹ᵁ D.map f₁ ⁻¹ᵁ U₁ ⊓ D.map f₃ ⁻¹ᵁ D.map f₂ ⁻¹ᵁ V₁) (V := ⊥)
    (TopologicalSpace.NoetherianSpace.isCompact _) (by
    rw [Scheme.Hom.preimage_inf, hw, hw, hw, hw, hU₁, hV₁]; exact hinf.le.trans bot_le)
  refine ⟨G.obj i₄, a i₄, hft _, hG _, cG.π.app i₄, π i₄,
    D.map f₄ ⁻¹ᵁ D.map f₃ ⁻¹ᵁ D.map f₁ ⁻¹ᵁ U₁, D.map f₄ ⁻¹ᵁ D.map f₃ ⁻¹ᵁ D.map f₂ ⁻¹ᵁ V₁,
    ha' _, (hπ _).w, ?_, ?_, ?_, ?_⟩
  · have := congr(D.map f₄ ⁻¹ᵁ $h₃)
    rw [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_sup] at this
    exact this
  · rw [Scheme.Hom.preimage_inf] at h₄
    exact le_bot_iff.1 h₄
  · exact ((hw f₄ _).trans ((hw f₃ _).trans (hw f₁ U₁))).trans hU₁
  · exact ((hw f₄ _).trans ((hw f₃ _).trans (hw f₂ V₁))).trans hV₁

theorem exists_mem_of_genericPoint_mem {T S : Scheme.{0}} [IsIntegral S] [IsNoetherian S]
    (t : T ⟶ S) [LocallyOfFiniteType t] [QuasiCompact t] {C : Set T} {Sg : Set S}
    (hC : Topology.IsConstructible C) (hSg : Dense Sg) (h : genericPoint S ∈ t '' C) :
    ∃ y ∈ C, t y ∈ Sg := by
  by_contra! H
  obtain ⟨V, hV, -, hd⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense T S t C Sg hC hSg
      (Set.disjoint_left.2 (by rintro _ ⟨y, hy, rfl⟩; exact H y hy))
  exact Set.disjoint_left.1 hd h
    (((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV))

theorem not_mem_image_inter {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : GeometricallyConnected (f.fiberToSpecResidueField (t y)))
    (U V : (pullback f t).Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    y ∉ (pullback.snd f t '' U) ∩ (pullback.snd f t '' V) := by
  rintro ⟨⟨u, hu, hu'⟩, v, hv, hv'⟩
  have : ConnectedSpace ((pullback.snd f t).fiber y) :=
    h.geometrically_connectedSpace _ _ _
      (isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback f t) y)
  have hc : _root_.IsPreconnected (pullback.snd f t ⁻¹' {y}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact isPreconnected_univ.image _ (Scheme.Hom.fiberι _ _).continuous.continuousOn
  have hsup' : (U : Set ↥(pullback f t)) ∪ V = Set.univ := by
    simpa using congr(($hsup : Set ↥(pullback f t)))
  have hinf' : (U : Set ↥(pullback f t)) ∩ V = ∅ := by
    simpa using congr(($hinf : Set ↥(pullback f t)))
  obtain ⟨z, -, hz⟩ := hc U V U.2 V.2 (hsup' ▸ Set.subset_univ _) ⟨u, hu', hu⟩ ⟨v, hv', hv⟩
  rw [hinf'] at hz
  exact hz

end GlobalTheory.GenericConnected

namespace GlobalTheory


open GenericConnected in
theorem geometricallyConnected_genericFibre_of_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (Sg : Set S), Dense Sg → (∀ x ∈ Sg, GeometricallyConnected (f.fiberToSpecResidueField x)) → GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S)) := by
  intro X S _ _ f _ _ Sg hSg hc
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have H : IsPullback (fst ≫ f.fiberι _) snd f (y ≫ S.fromSpecResidueField (genericPoint S)) :=
    h.paste_horiz (.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))
  have hy (z : Spec (.of K)) : (y ≫ S.fromSpecResidueField (genericPoint S)) z = genericPoint S := by
    rw [Scheme.Hom.comp_apply]
    exact (S.range_fromSpecResidueField _).le ⟨_, rfl⟩
  generalize y ≫ S.fromSpecResidueField (genericPoint S) = k at H hy
  generalize fst ≫ f.fiberι _ = g at H
  have hne : Nonempty Z := by
    have h1 : genericPoint S ∈ f '' Set.univ := by
      by_contra h0
      obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem (𝟙 S) (C := (f '' Set.univ)ᶜ)
        (f.isConstructible_image .univ).compl hSg ⟨_, h0, rfl⟩
      have := hc x hx'
      have : ConnectedSpace (f.fiber x) :=
        GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField x)
      obtain ⟨w⟩ : Nonempty (f.fiber x) := inferInstance
      exact hx ⟨_, trivial, (f.range_fiberι x).le ⟨w, rfl⟩⟩
    obtain ⟨x, -, hx⟩ := h1
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback H x (default : PrimeSpectrum K)
      (hx.trans (hy _).symm)
    exact ⟨z⟩
  suffices PreconnectedSpace Z from ⟨hne⟩
  refine ⟨fun U V hU hV hUV ⟨u, _, hu⟩ ⟨v, _, hv⟩ ↦ ?_⟩
  by_contra hemp
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hηW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint S)) isOpen_univ
  have : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hr : Set.range k ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hW.range_fromSpec, hy]
    exact hηW
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec k hr)
  have hk : Spec.map φ ≫ hW.fromSpec = k := by rw [hφ, IsOpenImmersion.lift_fac]
  algebraize [φ.hom]
  obtain ⟨T, a, _, _, b, π, U', V', hb, hπ, hsup, hinf, hU', hV'⟩ :=
    exists_spread (R := Γ(S, W)) (A := K) hW.fromSpec (p := f) (g := g) (q := snd) (by
      rw [← hk] at H; exact H) ⟨U, hU⟩ ⟨V, hV⟩
      (by ext; simpa using hUV trivial)
      (by ext z; simpa using fun h1 h2 ↦ hemp ⟨z, trivial, h1, h2⟩)
  let t : T ⟶ S := a ≫ hW.fromSpec
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian T := {}
  have : QuasiCompact t := inferInstance
  have : IsLocallyNoetherian (pullback f t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f t)
  have : CompactSpace ↥(pullback f t) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f t)
  have : IsNoetherian (pullback f t) := {}
  have hcons (O : (pullback f t).Opens) :
      Topology.IsConstructible (pullback.snd f t '' O) :=
    (pullback.snd f t).isConstructible_image
      (IsRetrocompact.isConstructible O.2 fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _)
  have hmem (O : (pullback f t).Opens) (z : Z) (hz : z ∈ π ⁻¹ᵁ O) :
      b (default : PrimeSpectrum K) ∈ pullback.snd f t '' O := by
    refine ⟨π z, hz, ?_⟩
    rw [← Scheme.Hom.comp_apply, hπ, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem t ((hcons U').inter (hcons V')) hSg
    ⟨b (default : PrimeSpectrum K), ⟨hmem U' u (hU' ▸ hu), hmem V' v (hV' ▸ hv)⟩, by
      have hbt : b ≫ t = k := by rw [← Category.assoc, hb]; exact hk
      exact (Scheme.Hom.comp_apply b t _).symm.trans ((congr($hbt _)).trans (hy _))⟩
  exact not_mem_image_inter f t x (hc _ hx') U' V' hsup hinf hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LeOfZpowMulUnitEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.PowCmp
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

def cstR (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem j_cstR (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  have h1 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (M.j ≫ M.Y.hom).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top
      = (A.hom ≫ spMap (algebraMap R K)).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    exact (Scheme.Hom.comp_appLE A.hom (spMap (algebraMap R K)) ⊤ _ _).symm
  have h3 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [h1, h2]; simp only [M.j_hom]
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h3
  exact h4.trans (congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm)

theorem not_isUnit_cstR [IsLocalRing R] (M : Model R A) (U : M.Y.left.Opens) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (cstR M U π) := by
  intro hu
  obtain ⟨y, hy, hs⟩ := h
  have h1 : M.Y.left.basicOpen (cstR M U π) = U := M.Y.left.basicOpen_of_isUnit hu
  have h2 : M.Y.left.basicOpen (cstR M U π) = U ⊓ M.Y.hom ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    Scheme.basicOpen_appLE M.Y.hom U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  rw [h1, basicOpen_eq_of_affine (R := CommRingCat.of R) π] at h2
  have h4 := (h2.le hy).2
  have h6 : M.Y.hom y = IsLocalRing.closedPoint R := hs
  have h7 : π ∉ PrimeSpectrum.asIdeal (M.Y.hom y) := h4
  rw [h6] at h7
  exact h7 hπ

theorem j_app_injective [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) :
    Function.Injective (M.j.app U).hom := by
  have := M.smooth
  have : IsDominant (spMap (algebraMap R K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsSchemeTheoreticallyDominant (pullback.fst M.Y.hom (spMap (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).flip
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsSchemeTheoreticallyDominant M.j := by unfold Model.j; infer_instance
  have : QuasiCompact M.j := by unfold Model.j; infer_instance
  exact M.j.app_injective U

end

theorem le_of_zpow_mul_unit_eq : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (M : Model R A) (W : M.Y.left.Opens), ((W : Set M.Y.left) ∩ M.sp).Nonempty → ∀ (σ s : Γ(M.Y.left, W)) (a b : ℤ), IsUnit σ → cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ a) * (M.j.app W).hom σ = cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ b) * (M.j.app W).hom s → b ≤ a := by
  intro R K _ _ _ _ _ _ π hirr A M U hU σ s a b hs e'
  by_contra hlt
  have hπ : π ∈ IsLocalRing.maximalIdeal R := hirr.not_isUnit
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hirr.ne_zero
  have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ a)) := (IsUnit.mk0 _ (zpow_ne_zero a hp)).map _
  rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cstR, ← map_mul] at e'
  have := j_app_injective M U (hu.mul_left_cancel e')
  rw [this, pow_succ, map_mul] at hs
  exact not_isUnit_cstR M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))

end GlobalTheory.SS.PowCmp
end
end
