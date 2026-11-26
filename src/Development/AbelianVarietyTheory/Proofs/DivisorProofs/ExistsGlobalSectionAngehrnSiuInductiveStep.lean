module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuNotKltAtSeveralPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsRestrictBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ)
    [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) →
    RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  intro Z _ q _ y hy r hr
  have hyt : y ∈ (⊤ : Z.Opens) := trivial
  obtain ⟨s, rfl⟩ := hr
  have hsurj : Function.Surjective ((Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤)) := by
    have e : (Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤) = (residueFieldIsoBase q y hy).inv.hom :=
      ReciprocityTheory.AnForm.R.constRes_eq q y hy
    rw [e]
    exact (residueFieldIsoBase q y hy).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨α, hα⟩ := hsurj (Z.residue y s)
  set g := Z.presheaf.germ ⊤ y hyt (algX q ⊤ α) with hgdef
  have hg : algebraMap (Z.presheaf.stalk y) Z.functionField g = GlobalTheory.Cartier.constFn q α := by
    rw [hgdef, algebraMap_germ]
    exact RingHom.congr_fun (fnOf_comp_algX q ⊤ _) α
  have hres : Z.residue y (s - g) = 0 := by
    rw [map_sub, sub_eq_zero, ← hα, hgdef, RingHom.comp_apply, ← Scheme.germ_residue, CommRingCat.comp_apply]
  have hnu : ¬ IsUnit (s - g) := by
    intro hu
    have : Z.residue y (s - g) ≠ 0 := by
      have := hu.map (Z.residue y).hom
      exact this.ne_zero
    exact this hres
  refine ⟨α, ?_⟩
  rw [← hg, ← map_sub]
  refine (nonUnit_iff (R := locRing y) ⟨_, s - g, rfl⟩).2 fun hu => hnu ?_
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨t, ht⟩ := u.2
  refine isUnit_iff_exists_inv.2 ⟨t, ?_⟩
  refine (IsFractionRing.injective (Z.presheaf.stalk y) Z.functionField ?_)
  rw [map_mul, map_one, ht]
  exact congrArg Subtype.val hu'

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPointStatement
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ) [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) → RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparated
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem specializes_of_locRing_le (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X)
    (h : locRing x ≤ locRing z) : z ⤳ x := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinjz : Function.Injective (algebraMap (X.presheaf.stalk z) X.functionField) :=
    IsFractionRing.injective _ _
  let ez : X.presheaf.stalk z ≃+* locRing z := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => hinjz (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  let φ : X.presheaf.stalk x →+* X.presheaf.stalk z :=
    ez.symm.toRingHom.comp
      ((Subring.inclusion h).comp (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict)
  have hφ (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk z) X.functionField (φ a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
    have e1 : ez (φ a) = Subring.inclusion h
        ((algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict a) := by
      exact ez.apply_symm_apply _
    exact congrArg Subtype.val e1
  have key : X.presheaf.stalkSpecializes hgx =
      CommRingCat.ofHom φ ≫ X.presheaf.stalkSpecializes hgz := by
    ext a
    exact (hφ a).symm
  let ι := Spec.map (X.presheaf.stalkSpecializes hgz)
  have hdom : IsDominant ι := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hgz).hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (X.presheaf.stalkSpecializes hgz).hom).1 hinjz]
    exact bot_le
  let g := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hfg : X.fromSpecStalk z = g := by
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from X)
      (Limits.terminal.hom_ext _ _) ι ?_
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]
    simp only [g, ι, ← Category.assoc, ← Spec.map_comp, ← key,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgx]
  have hz : z = g (IsLocalRing.closedPoint (X.presheaf.stalk z)) := by
    rw [← hfg, Scheme.fromSpecStalk_closedPoint]
  have hr : g (IsLocalRing.closedPoint (X.presheaf.stalk z)) ∈ Set.range (X.fromSpecStalk x) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Scheme.range_fromSpecStalk] at hr
  rw [hz]
  exact hr

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparatedStatement
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_of_pointLocalRing_le_separated : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X), locRing x ≤ locRing z → z ⤳ x := by
  first | exact @GlobalTheory.specializes_of_locRing_le | exact GlobalTheory.specializes_of_locRing_le | (intros; apply GlobalTheory.specializes_of_locRing_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResMap

def stalkEquiv {X : Scheme.{0}} [IsIntegral X] (x : X) : X.presheaf.stalk x ≃+* locRing x :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem residueMap : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  intro X _ _ p hp z k hk
  have hprop : IsProper p := by
    obtain ⟨N, j, hj, rfl⟩ := hp
    have := isProper_str ℂ N
    infer_instance
  have hsep : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from p]; infer_instance⟩
  obtain ⟨Z, i, hi, hZ, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  let q := i ≫ p
  have hrange : Set.range i = closure ({i (genericPoint Z)} : Set X) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hdim : topologicalKrullDim Z = k := by
    rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
    exact hk
  obtain ⟨-, w, hw⟩ := isLocModel_locRing_and_exists_trBasis Z q k (genericPoint Z) hdim
  letI alg : Algebra ℂ Z.functionField := (Cartier.constFn q).toAlgebra
  let π₀ : locRing (i (genericPoint Z)) →+* Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.comp (stalkEquiv (i (genericPoint Z))).symm.toRingHom
  refine ⟨Z.functionField, inferInstance, alg, π₀, ?_, ?_, ?_, ⟨w, hw⟩, ?_⟩
  · exact (i.stalkMap_surjective _).comp (stalkEquiv _).symm.surjective
  · intro r
    obtain ⟨a, rfl⟩ := (stalkEquiv _).surjective r
    have e1 : π₀ (stalkEquiv _ a) = (i.stalkMap (genericPoint Z)).hom a := by
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ a)) = _
      rw [RingEquiv.symm_apply_apply]
    have e2 : ((stalkEquiv _ a : locRing _) : X.functionField) = algebraMap _ _ a := rfl
    rw [e1, e2]
    constructor
    · intro h0
      refine ⟨a, ?_, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (i.stalkMap (genericPoint Z)).hom
      rw [h0] at this
      exact not_isUnit_zero this
    · rintro ⟨b, hb, e⟩
      obtain rfl := IsFractionRing.injective _ X.functionField e
      by_contra hne
      have hu : IsUnit ((i.stalkMap (genericPoint Z)).hom b) := isUnit_iff_ne_zero.2 hne
      exact (IsLocalRing.mem_maximalIdeal _).1 hb ((isUnit_map_iff _ _).1 hu)
  · intro a ha
    have hg := (algebraMap_germ (X := X) (x := i (genericPoint Z)) (U := ⊤) trivial (algX p ⊤ a)).trans
      (RingHom.congr_fun (fnOf_comp_algX p ⊤ (gen_mem (x := i (genericPoint Z)) trivial)) a)
    have hr : (⟨Cartier.constFn p a, ha⟩ : locRing _) =
        stalkEquiv _ (X.presheaf.germ ⊤ _ trivial (algX p ⊤ a)) := Subtype.ext hg.symm
    rw [hr]
    show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply]
    erw [Scheme.Hom.germ_stalkMap_apply i ⊤ (genericPoint Z) trivial (algX p ⊤ a)]
    have hc : (i.app ⊤).hom (algX p ⊤ a) = algX q (i ⁻¹ᵁ ⊤) a := by
      have e : (i ≫ p).appLE ⊤ (i ⁻¹ᵁ ⊤) (le_top.trans (Scheme.Hom.preimage_top _).ge) =
          p.appLE ⊤ ⊤ (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ i.appLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl := by
        first
          | rw [Scheme.Hom.appLE_comp_appLE]
          | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc,
              Scheme.Hom.naturality_assoc]; rfl)
      simp only [algX, q, RingHom.comp_apply]
      rw [Scheme.Hom.app_eq_appLE, e, CommRingCat.comp_apply]
    rw [hc]
    exact RingHom.congr_fun (fnOf_comp_algX q (i ⁻¹ᵁ ⊤) (gen_mem (x := genericPoint Z) trivial)) a
  · intro x h
    have hs : i (genericPoint Z) ⤳ x := GlobalTheory.T.specializes_of_pointLocalRing_le_separated X x _ h
    obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
      rw [hrange]; exact specializes_iff_mem_closure.mp hs
    have key : ∀ a : X.presheaf.stalk (i y),
        π₀ (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩) =
          algebraMap (Z.presheaf.stalk y) Z.functionField ((i.stalkMap y).hom a) := by
      intro a
      have e : (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩ : locRing _) =
          stalkEquiv _ ((X.presheaf.stalkSpecializes hs).hom a) := by
        apply Subtype.ext
        show algebraMap _ X.functionField a =
          algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hs).hom a)
        simp only [RingHom.algebraMap_toAlgebra]
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rw [e]
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
      rw [RingEquiv.symm_apply_apply]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) y
        ((genericPoint_spec Z).specializes trivial) a
    have hR : (π₀.comp (Subring.inclusion h)).range = locRing y := by
      ext f
      constructor
      · rintro ⟨⟨r, a, rfl⟩, rfl⟩
        exact ⟨(i.stalkMap y).hom a, (key a).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := i.stalkMap_surjective y b
        exact ⟨⟨_, a, rfl⟩, key a⟩
    have hloc : IsLocModel (Cartier.constFn q) (locRing y) := isLocModel_locRing y
    rw [hR]
    refine ⟨hloc, fun f => ?_, fun hx => ?_⟩
    · obtain ⟨a', ha', b', hb', hb0, e⟩ := hloc.frac f
      rw [← hR] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      exact ⟨a, b, hb0, e⟩
    · have hy : IsClosed ({y} : Set Z) := by
        have hpre : (i : Z → X) ⁻¹' {i y} = {y} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact i.isClosedEmbedding.injective.eq_iff
        rw [← hpre]
        exact hx.preimage i.continuous
      exact GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint Z q y hy

end GlobalTheory.ResMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueMap_closure_point : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  first | exact @GlobalTheory.ResMap.residueMap | exact GlobalTheory.ResMap.residueMap | (intros; apply GlobalTheory.ResMap.residueMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed_of_isProjOver : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  intro X _ p hP x hx
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hP
  exact ratRes_locRing_of_isClosed X p x hx

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem isLogEqn_changeForm_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  intro X _ _ p _ n hn Δ D η η' x m mD l gG fD g a F A δ t hη' hηF hm hmD hg hD hA
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'

  set gG' : X.functionFieldˣ := gG * F ^ (-(m : ℤ)) with hgG'
  have hord (E : DivOver p) : (E.ord gG' : ℚ) = E.ord gG - m * E.ord F := by
    rw [hgG', E.ord_mul, divOver_ord_zpow]
    push_cast
    ring
  have h1 : IsLogEqn p Δ η' x m gG' := by
    intro z hz E hE
    have e := hg z hz E hE
    rw [hηF, E.formOrd_smul hn hη' F] at e
    rw [hord, ← e]
    push_cast
    ring
  have hd1 (E : DivOver p) : discrep E η' m gG' = E.formOrd η' + E.ord F - E.ord gG / m := by
    rw [discrep, hord]
    field_simp
    ring

  obtain ⟨m₁, g₁, hm₁, h2, hd2⟩ := isLogEqn_add_smul X p n Δ D η' x m mD gG' fD (1 - δ) hm hmD h1 hD

  have hB : (CartierDiv.principal g + l • A).IsEqn x (g * a ^ l) :=
    (CartierDiv.isEqn_principal g x).add (hA.nsmul l)
  obtain ⟨V, hxV, hV⟩ := hB.exists_nhds
  have hD' : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal g + l • A) 1 z = (E.ord (g * a ^ l) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    rw [qWeil, (hV z (hz.mem_open V.isOpen hxV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, h3, hd3⟩ := isLogEqn_add_smul X p n (Δ + (1 - δ) • D)
    (qWeil (CartierDiv.principal g + l • A) 1) η' x m₁ 1 g₁ (g * a ^ l) t hm₁ Nat.one_pos h2 hD'
  refine ⟨m₂, g₂, hm₂, h3, fun E => ?_⟩
  rw [hd3, hd2, hd1]
  unfold DivOver.formOrd
  push_cast
  ring

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogCanonicalEquation_changeForm_perturbed_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  first | exact @GlobalTheory.PairStep.isLogEqn_changeForm_add | exact GlobalTheory.PairStep.isLogEqn_changeForm_add | (intros; apply GlobalTheory.PairStep.isLogEqn_changeForm_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancySubQCartierCoeffNonpos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancySubQCartierCoeffNonpos
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ)
    (Δ D : X → ℚ) (η : RatForms p n) (x : X) (m mD : ℕ) (gG fD : X.functionFieldˣ) (δ : ℚ),
    IsEffQDiv Δ → IsQCart D → δ ≤ 1 → 0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) →
    ∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing x) → discrep E η m gG - (1 - δ) * (E.ord fD / mD) ≤ 0 := by
  intro X _ _ _ p n Δ D η x m mD gG fD δ hΔ hD hδ hm hmD hlog hDz E hE
  obtain ⟨z, hzx, hEz⟩ := (isPrimeOf_placeEquiv E x).1 hE
  rw [hlog.discrep_eq_neg hm hzx hEz, ← hDz z hzx E hEz]
  have h1 : 0 ≤ Δ z := hΔ.nonneg z
  have h2 : 0 ≤ D z := by
    obtain ⟨m₀, D₀, -, hD₀, rfl⟩ := hD
    refine div_nonneg (Int.cast_nonneg ?_) (Nat.cast_nonneg m₀)
    obtain ⟨g, hg⟩ := D₀.exists_isEqn z
    obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hD₀ z g hg
    by_cases hz : Order.coheight z = 1
    · rw [hg.mult_eq, ← ha, ord_algebraMap hz fun h => g.ne_zero (by rw [← ha, h, map_zero])]
      exact Int.natCast_nonneg _
    · rw [hg.mult_eq, Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have h3 : 0 ≤ 1 - δ := by linarith
  nlinarith [mul_nonneg h3 h2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancySubQCartierCoeffNonposStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_sub_qCartier_coeff_nonpos : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ)
    (Δ D : X → ℚ) (η : RatForms p n) (x : X) (m mD : ℕ) (gG fD : X.functionFieldˣ) (δ : ℚ),
    IsEffQDiv Δ → IsQCart D → δ ≤ 1 → 0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) →
    ∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing x) → discrep E η m gG - (1 - δ) * (E.ord fD / mD) ≤ 0 := by
  first | exact @GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart | exact GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart | (intros; apply GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalScheme
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_locRing : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  intro X _ _ x
  let e : X.presheaf.stalk x ≃+* locRing x := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective _ X.functionField (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk x
  exact IsIntegrallyClosed.of_equiv e

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalSchemeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_pointLocalRing_normalScheme : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  first | exact @GlobalTheory.FieldPair.isIntegrallyClosed_locRing | exact GlobalTheory.FieldPair.isIntegrallyClosed_locRing | (intros; apply GlobalTheory.FieldPair.isIntegrallyClosed_locRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPoint
open GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isAlgebraic_of_mul_eq {S K : Type} [CommRing S] [Field K] [Algebra S K] {f : K} (a b : S)
    (hb : b ≠ 0) (e : f * algebraMap S K b = algebraMap S K a) : IsAlgebraic S f := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) h0
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ, sub_zero,
      Polynomial.coeff_zero, if_true] using h1
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem exists_trBasis_mem_of_isLocModel {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K)
    (n : ℕ) (hR : IsLocModel c R) (hx : ∃ x : Fin n → K, TrBasis c x) :
    ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  letI := c.toAlgebra
  obtain ⟨x, hx⟩ := hx
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (R : Set K)) K := by
    refine ⟨fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac f
    exact isAlgebraic_of_mul_eq (⟨a, Algebra.subset_adjoin ha⟩ : Algebra.adjoin ℂ (R : Set K))
      ⟨b, Algebra.subset_adjoin hb⟩ (fun h => hb0 (congrArg Subtype.val h)) e
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (R : Set K)
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) ht
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.trans h2.symm)
  refine ⟨fun j => ⟨(e j : K), hts (e j).2⟩, ?_⟩
  show IsTranscendenceBasis ℂ fun j => ((e j : t) : K)
  exact (isTranscendenceBasis_equiv e).2 ht

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPointStatement
open GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  first | exact @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | exact GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | (intros; apply GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionAngehrnSiuInductiveStep
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem unitAt_pow' {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (hf : UnitAt x f) :
    ∀ l : ℕ, UnitAt x (f ^ l)
  | 0 => by simpa using unitAt_one x
  | l + 1 => by rw [pow_succ]; exact (unitAt_pow' hf l).mul hf

theorem discrep_sub_ord_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ), topologicalKrullDim X = n → ∀ (Δ D : X → ℚ)
    (η η' : RatForms p n) (x z : X) (m m' mD : ℕ) (gG g' fD : X.functionFieldˣ) (E : DivOver p),
    η ≠ 0 → η' ≠ 0 → 0 < m → 0 < m' → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ w, w ⤳ x → ∀ E : DivOver p, E.IsAt w → D w = (E.ord fD : ℚ) / mD) →
    z ⤳ x → E.Through z → IsLogEqn p (Δ + D) η' z m' g' →
    discrep E η m gG - E.ord fD / mD = discrep E η' m' g' := by
  intro X _ _ _ p _ n hn Δ D η η' x z m m' mD gG g' fD E hη hη' hm hm' hmD hG hD hzx hE h'
  obtain ⟨m'', g'', hm'', h'', hd⟩ := isLogEqn_add_smul X p n Δ D η x m mD gG fD 1 hm hmD hG hD
  rw [one_smul] at h''
  have hz : IsLogEqn p (Δ + D) η z m'' g'' := fun w hw F hF => h'' w (hw.trans hzx) F hF
  rw [← discrep_eq hn hη hη' hm'' hm' hz h' hE, hd E, one_mul]

theorem not_kltAt_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (z x : X) (k l M r : ℕ) (h δ : ℚ)
      (f₀ : X.functionField) (aX : X.functionFieldˣ) (mD : ℕ) (fD : X.functionFieldˣ)
      {κ : Type} [Field κ] (π₀ : locRing z →+* κ) (hxz : locRing x ≤ locRing z)
      (w : Fin r → locRing x) (a : Fin r → ℂ),
    IsEffQDiv Δ → IsLogCanonicalMultiple p n Δ m G → 0 < m → IsQCart D → z ⤳ x → 0 < l → 0 ≤ h →
    0 ≤ δ → δ ≤ 1 → (∀ r, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) →
    A.IsEqn x aX → 0 < mD → RegAt x (fD : X.functionField) →
    (∀ w, w ⤳ x → ∀ E : DivOver p, E.IsAt w → D w = (E.ord fD : ℚ) / mD) →
    (∑ j, Cartier.constFn p (a j) * (w j : X.functionField)) = f₀ * (aX : X.functionField) ^ l →
    ((z = genericPoint X ∧ (k : ℚ) * l < h * M) ∨
      ∃ E : DivOver p, CentreAt E z ∧ (∃ (η' : RatForms p n) (m' : ℕ) (g' : X.functionFieldˣ), η' ≠ 0 ∧
        0 < m' ∧ IsLogEqn p (Δ + D) η' z m' g' ∧ discrep E η' m' g' ≤ -1) ∧
        (k : ℚ) + M * (δ * (E.ord fD / mD)) ≤ h / l * M) →
    (∀ (xi : Fin n → locRing x) (φ : locRing x →₀ ℚ) (u s : locRing x) (t : ℚ),
      TrBasis (Cartier.constFn p) (fun j => (xi j : X.functionField)) → (∀ g ∈ φ.support, g ≠ 0) →
      EffAt (Cartier.constFn p) n (locRing x) (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
        (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) →
      π₀.comp (Subring.inclusion hxz) u = 0 → 0 ≤ t →
      (s : X.functionField) = ∑ j, Cartier.constFn p (a j) * (w j : X.functionField) + u →
      (s : X.functionField) ≠ 0 →
      ((Function.Injective (π₀.comp (Subring.inclusion hxz)) ∧ (k : ℚ) ≤ t * M) ∨
        ∃ E : Place (Cartier.constFn p), E.Contains (locRing x) ∧
          (∀ r : locRing x, (r : X.functionField) ≠ 0 →
            (π₀.comp (Subring.inclusion hxz) r = 0 ↔ 0 < E.ord r)) ∧
          (k : ℚ) + M * (E.disc (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
            (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) + 1) ≤ t * M) →
      ¬ Klt (Cartier.constFn p) n (locRing x) (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
        (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ +
          Finsupp.single (s : X.functionField) t)) →
    ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u → ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u →
      ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  intro X _ _ _ p n hp hn Δ m G A D z x k l M r h δ f₀ aX mD fD κ _ π₀ hxz w a hΔ hG hm hD hzx hl hh
    hδ0 hδ1 hπ hA hmD hfD hDx hw hcase H u hu hvan g hg hK
  haveI := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hp
  have hLM : IsLocModel (Cartier.constFn p) (locRing x) := isLocModel_locRing x
  obtain ⟨-, hx0⟩ := isLocModel_locRing_and_exists_trBasis X p n x hn
  obtain ⟨xi, hxi⟩ := GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint (Cartier.constFn p) (locRing x) n hLM hx0
  have hfree := isFreeGen_dForm_of_trBasis (Cartier.constFn p) hxi
  have hω0 : dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) ≠ 0 := fun h0 =>
    one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  obtain ⟨η, hη, hGη⟩ := hG
  obtain ⟨gG, hgG⟩ := G.exists_isEqn x
  have hLE := hGη x gG hgG
  obtain ⟨F0, hF0⟩ := hfree.2 η
  replace hF0 : F0 • dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) = η := hF0
  have hF0ne : F0 ≠ 0 := fun h0 => hη (by rw [← hF0, h0, zero_smul])
  obtain ⟨m₂, g₂, hm₂, hLE₂, hdisc₂⟩ := GlobalTheory.T.isLogCanonicalEquation_changeForm_perturbed_divisor X p n hn Δ D η
    (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField))) x m mD l gG fD g aX
    (Units.mk0 F0 hF0ne) A δ (h / l) hω0 hF0.symm hm hmD hLE hDx hA
  have hKlt := (kltAt_iff_klt (p := p) hn hω0 hm₂ hLE₂).1 hK

  have hAz : A.IsEqn z aX := by
    obtain ⟨U, hxU, hU⟩ := hA.exists_nhds
    exact hU z (hzx.mem_open U.isOpen hxU)
  have hAl := hA.nsmul l
  have hAlz := hAz.nsmul l

  have hsum : (f₀ * (aX : X.functionField) ^ l) ∈ locRing x := by
    rw [← hw]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hLM.const_mem _) (w j).2
  have hux : u * (aX : X.functionField) ^ l ∈ locRing x := by
    have := (hAl.regularAt_iff).1 ((CartierDiv.mem_sections).1 hu x)
    exact mem_locRing.2 (by simpa using this)
  have hgx : (g : X.functionField) * (aX : X.functionField) ^ l ∈ locRing x := by
    rw [hg, add_mul]; exact Subring.add_mem _ hsum hux
  have huz : ZeroAt z (u * (aX : X.functionField) ^ l) := by
    have := (hAlz.vanishesAt_iff).1 hvan
    simpa using this

  set ω := dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) with hω
  have hmR : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  set q : X.functionField := (gG : X.functionField) * (F0 ^ m)⁻¹ with hq
  have hq0 : q ≠ 0 := mul_ne_zero gG.ne_zero (inv_ne_zero (pow_ne_zero _ hF0ne))
  obtain ⟨a₁, ha₁, b₁, hb₁, hb0, hab⟩ := hLM.frac q
  have ha0 : a₁ ≠ 0 := by rw [← hab]; exact mul_ne_zero hq0 hb0
  let φ : locRing x →₀ ℚ := Finsupp.single ⟨a₁, ha₁⟩ (1 / m : ℚ) - Finsupp.single ⟨b₁, hb₁⟩ (1 / m : ℚ) +
    Finsupp.single ⟨(fD : X.functionField), hfD⟩ ((1 - δ) / mD)
  have hmap : Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ =
      Finsupp.single a₁ (1 / m : ℚ) - Finsupp.single b₁ (1 / m : ℚ) +
        Finsupp.single (fD : X.functionField) ((1 - δ) / mD) := by
    simp only [φ, Finsupp.mapDomain_add, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφ0 : ∀ g ∈ φ.support, g ≠ 0 := by
    rintro g hgs rfl
    apply Finsupp.mem_support_iff.1 hgs
    have e1 : (⟨a₁, ha₁⟩ : locRing x) ≠ 0 := fun e => ha0 (congrArg Subtype.val e)
    have e2 : (⟨b₁, hb₁⟩ : locRing x) ≠ 0 := fun e => hb0 (congrArg Subtype.val e)
    have e3 : (⟨(fD : X.functionField), hfD⟩ : locRing x) ≠ 0 := fun e => fD.ne_zero (congrArg Subtype.val e)
    simp [φ, Finsupp.single_apply, e1, e2, e3]
  have hord (E : Place (Cartier.constFn p)) : (E.ord a₁ : ℚ) - E.ord b₁ = E.ord gG - m * E.ord F0 := by
    have h1 : E.ord a₁ = E.ord q + E.ord b₁ := by rw [← hab, E.ord_mul hq0 hb0]
    have h2 : E.ord q = E.ord gG - m * E.ord F0 := by
      rw [hq, E.ord_mul gG.ne_zero (inv_ne_zero (pow_ne_zero _ hF0ne)), E.ord_inv, E.ord_pow]; ring
    rw [h1, h2]; push_cast; ring
  have hdψ (E : Place (Cartier.constFn p)) : E.disc ω (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) =
      E.formOrd η - E.ord gG / m - (1 - δ) * (E.ord fD / mD) := by
    rw [Place.disc, hmap, map_add (f := _), map_sub, Place.ordQ_single, Place.ordQ_single, Place.ordQ_single, ← hF0,
      E.formOrd_smul hxi hω0 hF0ne]
    have := hord E
    have e : (1 / (m : ℚ)) * E.ord a₁ - 1 / m * E.ord b₁ = E.ord gG / m - E.ord F0 := by
      rw [← mul_sub, this]; field_simp
    push_cast
    linear_combination -e
  have hdψs (E : Place (Cartier.constFn p)) (ψ : X.functionField →₀ ℚ) (s : X.functionField) (t : ℚ) :
      E.disc ω (ψ + Finsupp.single s t) = E.disc ω ψ - t * E.ord s := by
    rw [Place.disc, Place.disc, map_add (f := _), Place.ordQ_single]; ring
  have hs0 : (g : X.functionField) * (aX : X.functionField) ^ l ≠ 0 :=
    mul_ne_zero g.ne_zero (pow_ne_zero _ aX.ne_zero)
  have hψ0 : Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ 0 = 0 := by
    rw [hmap]; simp [Finsupp.single_apply, ha0, hb0, fD.ne_zero]

  have hK2 : Klt (Cartier.constFn p) n (locRing x) ω
      (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ +
        Finsupp.single ((g : X.functionField) * (aX : X.functionField) ^ l) (h / l)) := by
    refine ⟨hω0, ?_, fun E hE => ?_⟩
    · rw [Finsupp.add_apply, hψ0]; simp [Finsupp.single_apply, hs0]
    · obtain ⟨E', rfl⟩ := (placeEquiv p).surjective E
      have h1 := hKlt.lt_disc hE
      rw [disc_placeEquiv, hdisc₂ E'] at h1
      change -1 < (E'.formOrd ω : ℚ) + E'.ord (Units.mk0 F0 hF0ne) -
        E'.ord gG / m - (1 - δ) * (E'.ord fD / mD) -
        h / l * E'.ord (g * aX ^ l) at h1
      rw [hdψs, hdψ, ← hF0, (placeEquiv p E').formOrd_smul hxi hω0 hF0ne]
      have e1 : (placeEquiv p E').ord ((g : X.functionField) * (aX : X.functionField) ^ l) =
          E'.ord (g * aX ^ l) := by rw [← ord_placeEquiv]; push_cast; rfl
      have e2 : (placeEquiv p E').ord F0 = E'.ord (Units.mk0 F0 hF0ne) := rfl
      have e3 : (placeEquiv p E').formOrd ω = E'.formOrd ω := rfl
      have e4 : (placeEquiv p E').ord (gG : X.functionField) = E'.ord gG := rfl
      have e5 : (placeEquiv p E').ord (fD : X.functionField) = E'.ord fD := rfl
      rw [e1, e2, e3, e4, e5]
      push_cast
      linarith
  have hEff : EffAt (Cartier.constFn p) n (locRing x) ω
      (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) := by
    refine ⟨hω0, hψ0, fun E hE => ?_⟩
    obtain ⟨E', rfl⟩ := (placeEquiv p).surjective E
    have h1 := GlobalTheory.T.discrepancy_sub_qCartier_coeff_nonpos X p n Δ D η x m mD gG fD δ hΔ hD hδ1 hm hmD hLE hDx E' hE
    rw [hdψ]
    exact h1
  refine H xi φ ⟨u * (aX : X.functionField) ^ l, hux⟩ ⟨(g : X.functionField) * (aX : X.functionField) ^ l, hgx⟩
    (h / l) hxi hφ0 hEff ((hπ _).2 huz) (div_nonneg hh (Nat.cast_nonneg _)) ?_ hs0 ?_ hK2
  · show (g : X.functionField) * (aX : X.functionField) ^ l = _ + u * (aX : X.functionField) ^ l
    rw [hw, hg]; ring
  rcases hcase with ⟨rfl, hkl⟩ | ⟨E, hC, ⟨η', m', g', hη', hm', hLE', hle⟩, hbd⟩
  · refine Or.inl ⟨(injective_iff_map_eq_zero _).2 fun r hr => ?_, ?_⟩
    · have hz := (hπ _).1 hr
      by_contra hr0
      have hr0' : (r : X.functionField) ≠ 0 := fun e => hr0 (Subtype.ext e)
      exact (zeroAt_iff.1 hz).2 (unitAt_genericPoint hr0')
    · have hlR : (0 : ℚ) < l := by exact_mod_cast hl
      rw [div_mul_eq_mul_div, le_div_iff₀ hlR]
      linarith
  · refine Or.inr ⟨placeEquiv p E, (contains_placeEquiv E x).2 (hC.1.of_specializes hzx), fun r hr0 => ?_, ?_⟩
    · have hrz : RegAt z (r : X.functionField) := hxz r.2
      change π₀ (Subring.inclusion hxz r) = 0 ↔ 0 < E.ord (Units.mk0 (r : X.functionField) hr0)
      rw [hπ]
      change ZeroAt z (r : X.functionField) ↔ _
      constructor
      · intro hz0
        have h0 : 0 ≤ E.ord (Units.mk0 (r : X.functionField) hr0) :=
          (E.ord_nonneg_iff _).2 (hC.1 _ hrz)
        rcases h0.lt_or_eq with h0 | h0
        · exact h0
        · exfalso
          have hi := hC.2 (Units.mk0 (r : X.functionField) hr0) hrz h0.symm
          have hU : UnitAt z (r : X.functionField) := (unitAt_iff hr0).2 ⟨hrz, by simpa using hi⟩
          exact (zeroAt_iff.1 hz0).2 hU
      · intro hpos
        refine zeroAt_iff.2 ⟨hrz, fun hU => ?_⟩
        have hi := hU.inv.regAt
        have h0 := (E.ord_nonneg_iff (Units.mk0 (r : X.functionField) hr0)⁻¹).2 (hC.1 _ (by simpa using hi))
        rw [E.ord_inv] at h0
        omega
    · rw [hdψ]
      have key := discrep_sub_ord_eq X p n hn Δ D η η' x z m m' mD gG g' fD E hη hη' hm hm' hmD hLE hDx hzx
        hC.1 hLE'
      have e3 : (placeEquiv p E).formOrd η = E.formOrd η := rfl
      have e4 : (placeEquiv p E).ord (gG : X.functionField) = E.ord gG := rfl
      have e5 : (placeEquiv p E).ord (fD : X.functionField) = E.ord fD := rfl
      rw [e3, e4, e5]
      have hd : (E.formOrd η : ℚ) - E.ord gG / m = discrep E η m gG := rfl
      have hM : (0 : ℚ) ≤ M := Nat.cast_nonneg _
      have hb : (E.formOrd η : ℚ) - E.ord gG / m - (1 - δ) * (E.ord fD / mD) + 1 ≤ δ * (E.ord fD / mD) := by
        rw [hd]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hb hM]

theorem exists_global_step : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ),
  IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
  ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
  IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) → IsQCart D →
  (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k →
  (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
  (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∀ l₀ : ℕ, ∃ l : ℕ, l₀ ≤ l ∧ h < l ∧ ∃ f₀ ∈ (l • A).sections, (l • A).GeneratesAt z f₀ ∧
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u →
      ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P,
        ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  intro hPr X _ _ _ p n hp hn Δ m G A D P z k h hΔ _ hm hG hA hD hP hk hZ hcase hh hnum l₀
  haveI := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hp

  obtain ⟨q, hq, hnumq⟩ := GlobalTheory.T.exists_lt_binomial_bound_of_mul_pow_lt P.card k h _ hk hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv X p hp A z k q hA hZ hq
  obtain ⟨l₂, hl₂⟩ := exists_sections_restrict_basis X p hp A z hA
  obtain ⟨l, M, hl0, hM, hkl, hhl, hcl⟩ := hnumq (max l₀ (max l₁ l₂))
  obtain ⟨r, f, hfs, hr, hgen⟩ := hl₂ l ((le_max_right _ _).trans ((le_max_right _ _).trans hl0))
  have hq1 := hl₁ l ((le_max_left _ _).trans ((le_max_right _ _).trans hl0))
  have hcr : P.card * (M + k - 1).choose k < r := by
    have : ((P.card * (M + k - 1).choose k : ℕ) : ℚ) < r := by rw [hr]; exact lt_of_lt_of_le hcl hq1
    exact_mod_cast this

  obtain ⟨κ, _, _, π₀, -, hπ, hconst, hκ, hloc⟩ := GlobalTheory.T.exists_residueMap_closure_point X p hp z k hZ
  letI : Algebra ℂ X.functionField := (Cartier.constFn p).toAlgebra
  choose aX haX using fun x : X => A.exists_isEqn x
  obtain ⟨aZ, haZ⟩ := A.exists_isEqn z
  choose mD fD hmD hfD hDx using fun x : X => exists_localEqn_of_isQCart X p D hD x
  let e : Fin P.card ≃ P := P.equivFin.symm
  have hxz : ∀ i, locRing (e i : X) ≤ locRing z := fun i f hf =>
    regAt_of_specializes (hP _ (e i).2).2 hf
  have hAz : ∀ i, A.IsEqn z (aX (e i)) := fun i => by
    obtain ⟨U, hxU, hU⟩ := (haX (e i)).exists_nhds
    exact hU z ((hP _ (e i).2).2.mem_open U.isOpen hxU)
  have hunit : ∀ i, UnitAt z ((aX (e i) : X.functionField) ^ l / (aZ : X.functionField) ^ l) := fun i => by
    rw [← div_pow]
    exact unitAt_pow' ((haZ.iff_unitAt).1 (hAz i)) l
  have hwreg : ∀ i j, f j * (aX (e i) : X.functionField) ^ l ∈ locRing (e i : X) := fun i j => by
    have := ((haX (e i)).nsmul l).regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) _)
    exact mem_locRing.2 (by simpa using this)
  have hwbreg : ∀ j, f j * (aZ : X.functionField) ^ l ∈ locRing z := fun j => by
    have := (haZ.nsmul l).regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) _)
    exact mem_locRing.2 (by simpa using this)
  let π : ∀ i, locRing (e i : X) →+* κ := fun i => π₀.comp (Subring.inclusion (hxz i))
  let w : ∀ i, Fin r → locRing (e i : X) := fun i j => ⟨_, hwreg i j⟩
  let lam : Fin P.card → κ := fun i => π₀ ⟨_, (hunit i).regAt⟩
  let wb : Fin r → κ := fun j => π₀ ⟨_, hwbreg j⟩
  have hlamw : ∀ i, lam i ≠ 0 ∧ ∀ j, π i (w i j) = lam i * wb j := fun i => by
    refine ⟨fun h0 => (zeroAt_iff.1 ((hπ _).1 h0)).2 (hunit i), fun j => ?_⟩
    show π₀ (Subring.inclusion (hxz i) (w i j)) = _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show f j * (aX (e i) : X.functionField) ^ l =
      (aX (e i) : X.functionField) ^ l / (aZ : X.functionField) ^ l * (f j * (aZ : X.functionField) ^ l)
    have : (aZ : X.functionField) ^ l ≠ 0 := pow_ne_zero _ aZ.ne_zero
    field_simp

  obtain ⟨av, hav, hfam⟩ := GlobalTheory.T.angehrnSiu_not_klt_at_several_points hPr n k P.card r M (fun i => locRing (e i : X)) π w lam wb
    (isLocModel_locRing_and_exists_trBasis X p n z hn).2 hκ hk
    (fun i => ⟨isLocModel_locRing _, GlobalTheory.T.isIntegrallyClosed_pointLocalRing_normalScheme X _, GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex X p hp _ (hP _ (e i).2).1⟩)
    (fun i a h => hconst a (hxz i h)) (fun i f => (hloc _ (hxz i)).2.1 f)
    (fun i => ⟨(hloc _ (hxz i)).1, (hloc _ (hxz i)).2.2 (hP _ (e i).2).1⟩) hlamw hcr hM

  have hf₀ : (∑ j, Cartier.constFn p (av j) * f j) ∈ (l • A).sections := by
    rw [CartierDiv.mem_sections]
    intro x
    obtain ⟨g0, hg0⟩ := (l • A).exists_isEqn x
    rw [hg0.regularAt_iff, Finset.sum_mul]
    refine Subring.sum_mem (locRing x) fun j _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ ((isLocModel_locRing x).const_mem _)
      (mem_locRing.2 (hg0.regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) x)))
  have hMpos : (0 : ℚ) < M := by exact_mod_cast hM
  have hlpos : (0 : ℚ) < l := lt_trans hh hhl
  have hl : 0 < l := by exact_mod_cast hlpos
  have hgap : 0 < h / l * M - k := by
    rw [div_mul_eq_mul_div, sub_pos, lt_div_iff₀ hlpos]
    linarith
  have hwsum : ∀ i, (∑ j, Cartier.constFn p (av j) * (w i j : X.functionField)) =
      (∑ j, Cartier.constFn p (av j) * f j) * (aX (e i) : X.functionField) ^ l := fun i => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Cartier.constFn p (av j) * (f j * (aX (e i) : X.functionField) ^ l) = _
    ring
  have hei : ∀ x (hx : x ∈ P), (e (P.equivFin ⟨x, hx⟩) : X) = x := fun x hx => by simp [e]
  refine ⟨l, (le_max_left _ _).trans hl0, hhl, _, hf₀, hgen av hav, ?_⟩
  rcases hcase with hgenz | ⟨E, η', m', g', hη', hm', hLE', hC, hdle⟩
  · refine ⟨1, one_pos, le_rfl, fun u hu hvan g hg δ hδ0 hδ1 x hx => ?_⟩
    have := not_kltAt_of_local X p n hp hn Δ m G A D z (e (P.equivFin ⟨x, hx⟩)) k l M r h δ _
      (aX _) (mD _) (fD _) π₀ (hxz _) (w _) av hΔ hG hm hD (hP _ (e _).2).2 hl hh.le hδ0 hδ1 hπ (haX _)
      (hmD _) (hfD _) (hDx _) (hwsum _) (Or.inl ⟨hgenz, hkl⟩) (hfam _) u hu hvan g hg
    rwa [hei x hx] at this
  · have hnn : ∀ x ∈ P, (0 : ℚ) ≤ E.ord (fD x) / mD x := fun x hx => by
      have h0 : 0 ≤ E.ord (fD x) :=
        (E.ord_nonneg_iff _).2 (hC.1.of_specializes (hP x hx).2 _ (hfD x))
      positivity
    set B : ℚ := ∑ x ∈ P, (E.ord (fD x) : ℚ) / mD x with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg hnn
    refine ⟨min 1 ((h / l * M - k) / (M * (B + 1))), lt_min one_pos (div_pos hgap (by positivity)),
      min_le_left _ _, fun u hu hvan g hg δ hδ0 hδ x hx => ?_⟩
    have hbx : (E.ord (fD x) : ℚ) / mD x ≤ B + 1 := by
      have := Finset.single_le_sum hnn hx
      linarith
    have h1 : δ * (M * (B + 1)) ≤ h / l * M - k :=
      (le_div_iff₀ (by positivity)).1 (hδ.trans (min_le_right _ _))
    have h2 : M * (δ * (E.ord (fD x) / mD x)) ≤ δ * (M * (B + 1)) := by
      have := mul_le_mul_of_nonneg_left hbx (mul_nonneg hMpos.le hδ0)
      nlinarith
    have hbd : (k : ℚ) + M * (δ * (E.ord (fD x) / mD x)) ≤ h / l * M := by linarith
    rw [← hei x hx] at hbd
    have := not_kltAt_of_local X p n hp hn Δ m G A D z (e (P.equivFin ⟨x, hx⟩)) k l M r h δ _
      (aX _) (mD _) (fD _) π₀ (hxz _) (w _) av hΔ hG hm hD (hP _ (e _).2).2 hl hh.le hδ0
      (hδ.trans (min_le_left _ _)) hπ (haX _) (hmD _) (hfD _) (hDx _) (hwsum _)
      (Or.inr ⟨E, hC, ⟨η', m', g', hη', hm', hLE', hdle⟩, hbd⟩) (hfam _) u hu hvan g hg
    rwa [hei x hx] at this

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionAngehrnSiuInductiveStepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ),
  IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
  ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
  IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) → IsQCart D →
  (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k →
  (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
  (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∀ l₀ : ℕ, ∃ l : ℕ, l₀ ≤ l ∧ h < l ∧ ∃ f₀ ∈ (l • A).sections, (l • A).GeneratesAt z f₀ ∧
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u →
      ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P,
        ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  first | exact @GlobalTheory.PairStep.exists_global_step | exact GlobalTheory.PairStep.exists_global_step | (intros; apply GlobalTheory.PairStep.exists_global_step <;> assumption)
end
