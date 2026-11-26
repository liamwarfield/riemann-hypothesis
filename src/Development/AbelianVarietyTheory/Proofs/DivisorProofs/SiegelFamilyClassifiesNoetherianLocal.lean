module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_localArtinian_point_eq (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P]
    (x y : Spec P) : x = y := by
  apply PrimeSpectrum.ext
  haveI := x.isPrime
  haveI := y.isPrime
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)]

theorem spec_map_injective_of_surjective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Surjective f) :
    Function.Injective (Spec.map f) := fun x y h =>
  PrimeSpectrum.comap_injective_of_surjective f.hom hf h

theorem spec_pullback_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  intro P B₁ B₂ B₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ hnt Z a b hab
  have hnt₁ : Nontrivial B₁ := RingHom.domain_nontrivial g₁.hom
  have hnt₂ : Nontrivial B₂ := RingHom.domain_nontrivial g₂.hom
  obtain ⟨y₀⟩ : Nonempty (Spec B₀) := inferInstanceAs (Nonempty (PrimeSpectrum B₀))
  have hone₁ : ∀ y y' : Spec B₁, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₁ hs₁ (spec_localArtinian_point_eq P _ _)
  have hone₂ : ∀ y y' : Spec B₂, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₂ hs₂ (spec_localArtinian_point_eq P _ _)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := a (Spec.map g₁ y₀)) trivial
  have hza : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩; rw [hV.range_fromSpec, hone₁ y (Spec.map g₁ y₀)]; exact hzV
  have hzb : Set.range b ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec, hone₂ y (Spec.map g₂ y₀)]
    have : b (Spec.map g₂ y₀) = a (Spec.map g₁ y₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
    rw [this]; exact hzV
  haveI := hV.isOpenImmersion_fromSpec
  set φ₁ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec a hza) with hφ₁
  set φ₂ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec b hzb) with hφ₂
  have ha : Spec.map φ₁ ≫ hV.fromSpec = a := by
    rw [hφ₁, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map φ₂ ≫ hV.fromSpec = b := by
    rw [hφ₂, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφ : φ₁ ≫ g₁ = φ₂ ≫ g₂ := by
    apply Spec.map_injective
    rw [← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha, hb, hab]
  have key : ∀ w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a → Spec.map f₂ ≫ w = b →
      w = Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec := by
    intro w hw₁ hw₂
    have hr : Set.range w ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨x, rfl⟩
      rw [spec_localArtinian_point_eq P x (Spec.map f₁ (Spec.map g₁ y₀)), ← Scheme.Hom.comp_apply, hw₁]
      exact hza ⟨_, rfl⟩
    rw [← IsOpenImmersion.lift_fac hV.fromSpec w hr, ← Spec.map_preimage (IsOpenImmersion.lift hV.fromSpec w hr)]
    congr 2
    apply hP.hom_ext
    · rw [IsPullback.lift_fst]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₁, ha]
    · rw [IsPullback.lift_snd]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₂, hb]
  refine ⟨Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec, ⟨?_, ?_⟩, fun w hw => key w hw.1 hw.2⟩
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_fst, ha]
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_snd, hb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUniqueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  first | exact @GlobalTheory.spec_pullback_localArtinian_glue_existsUnique | exact GlobalTheory.spec_pullback_localArtinian_glue_existsUnique | (intros; apply GlobalTheory.spec_pullback_localArtinian_glue_existsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmall
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SmallClassify

theorem lift_lemma : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e * e = 0 → ∀ (β : R →+* C) (x₀ : Sp (C ⧸ Ideal.span {e}) ⟶ X), x₀ ≫ s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) → ∃ x₁ : Sp C ⟶ X, x₁ ≫ s = spMap β ∧ spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ x₁ = x₀ := by
  intro R _ X s d hs C _ _ e hee β x₀ hx₀
  haveI : Smooth s := hs.smooth
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hsurj : Function.Surjective πC := Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (Spec.map πC) := IsClosedImmersion.spec_of_surjective _ hsurj
  have hnil : IsNilpotent (RingHom.ker πC.hom) := by
    refine ⟨2, ?_⟩
    show (RingHom.ker (Ideal.Quotient.mk (Ideal.span {e}))) ^ 2 = ⊥
    rw [Ideal.mk_ker, pow_two, Ideal.span_singleton_mul_span_singleton, hee, Ideal.span_singleton_eq_bot.2 rfl]
  have hw : x₀ ≫ s = Spec.map πC ≫ spMap β := by
    rw [hx₀, GlobalTheory.SiegelRingChange.spMap_comp']
  obtain ⟨W, hW, l, hl, hl'⟩ := GlobalTheory.exists_local_lift_of_smooth s (Spec.map πC) (GlobalTheory.isNilpotent_ker_specMap πC hnil)
    x₀ (spMap β) hw (IsLocalRing.closedPoint (CommRingCat.of C))
  have hWt : W = ⊤ := (IsLocalRing.closed_point_mem_iff (R := CommRingCat.of C) (U := W)).mp hW
  subst hWt
  haveI : IsIso (⊤ : (Sp C).Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have hU : IsIso ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  refine ⟨inv (⊤ : (Sp C).Opens).ι ≫ l, by rw [Category.assoc, hl, IsIso.inv_hom_id_assoc], ?_⟩
  rw [← cancel_epi ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι, ← hl', ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (⊤ : (Sp C).Opens).ι, Category.assoc, IsIso.inv_hom_id, Category.comp_id, morphismRestrict_ι]

theorem isPullback_of_bij {P A B D : CommRingCat.{0}} (f₁ : P ⟶ A) (f₂ : P ⟶ B) (g₁ : A ⟶ D) (g₂ : B ⟶ D)
    (w : f₁ ≫ g₁ = f₂ ≫ g₂) (hinj : ∀ x, f₁ x = 0 → f₂ x = 0 → x = 0)
    (hsurj : ∀ a b, g₁ a = g₂ b → ∃ x, f₁ x = a ∧ f₂ x = b) : IsPullback f₁ f₂ g₁ g₂ := by
  have hw : ∀ x, g₁ (f₁ x) = g₂ (f₂ x) := fun x => by
    have := congrArg (fun h : P ⟶ D => h x) w
    simpa using this
  let Q := RingHom.eqLocus (g₁.hom.comp (RingHom.fst A B)) (g₂.hom.comp (RingHom.snd A B))
  let φ : P →+* Q := (f₁.hom.prod f₂.hom).codRestrict Q (fun x => hw x)
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).2 fun x hx => hinj x ?_ ?_, fun y => ?_⟩
    · exact congrArg (fun z : Q => (z : A × B).1) hx
    · exact congrArg (fun z : Q => (z : A × B).2) hx
    · obtain ⟨x, h1, h2⟩ := hsurj (y : A × B).1 (y : A × B).2 y.2
      exact ⟨x, Subtype.ext (Prod.ext h1 h2)⟩
  let E : P ≅ CommRingCat.of Q := (RingEquiv.ofBijective φ hφ).toCommRingCatIso
  have h0 := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit g₁ g₂)
  refine IsPullback.of_iso h0 E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).1 = f₁ (E.inv (φ x))
    rw [this]; rfl
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).2 = f₂ (E.inv (φ x))
    rw [this]; rfl


open IsLocalRing in
theorem ring_lemma : ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : CommRingCat.{0}) (i : CommRingCat.of C ⟶ P) (p σ : P ⟶ CommRingCat.of C) (q : P ⟶ CommRingCat.of (DualNumber (IsLocalRing.ResidueField C))), i ≫ p = 𝟙 _ ∧ i ≫ σ = 𝟙 _ ∧ IsPullback p σ (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ∧ IsPullback p q (CommRingCat.ofHom (IsLocalRing.residue C)) (CommRingCat.ofHom (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C)).toRingHom) ∧ IsLocalRing P ∧ IsArtinianRing P ∧ Function.Surjective p ∧ Function.Surjective q := by
  intro C _ _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let dF : DualNumber (ResidueField C) →+* ResidueField C :=
    (TrivSqZeroExt.fstHom (ResidueField C) (ResidueField C) (ResidueField C)).toRingHom
  let Ps : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) (dF.comp (RingHom.snd _ _))
  let p : Ps →+* C := (RingHom.fst _ _).comp Ps.subtype
  let q : Ps →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp Ps.subtype
  let i : C →+* Ps := RingHom.codRestrict ((RingHom.id C).prod
    ((algebraMap (ResidueField C) (DualNumber (ResidueField C))).comp (residue C))) Ps (fun c ↦ rfl)
  let σ : Ps →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add (f := _)]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add (f := _), hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩

  have hunit : ∀ x : Ps, IsUnit (x : C × DualNumber (ResidueField C)).1 → IsUnit x := by
    rintro ⟨⟨a, y⟩, hx⟩ ha
    have hx' : residue C a = y.fst := hx
    have hy : IsUnit y := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hx']
      exact ha.map _
    obtain ⟨u, hu⟩ := (Prod.isUnit_iff (x := (a, y))).2 ⟨ha, hy⟩
    have hmem : ((u⁻¹ : (C × DualNumber (ResidueField C))ˣ) : C × DualNumber (ResidueField C)) ∈ Ps := by
      show ((residue C).comp (RingHom.fst _ _)) _ = (dF.comp (RingHom.snd _ _)) _
      rw [map_units_inv, map_units_inv, hu]
      exact congrArg (·⁻¹) hx
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show (a, y) * _ = 1
    rw [← hu, Units.mul_inv]
  haveI : Nontrivial Ps := nontrivial_of_ne 0 1 (fun h ↦ zero_ne_one (α := C) (congrArg (fun z : Ps ↦ (z : C × DualNumber (ResidueField C)).1) h))
  have hloc : IsLocalRing Ps := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (x : C × DualNumber (ResidueField C)).1).imp (hunit x) (fun h ↦ hunit (1 - x) (by simpa using h))

  letI : Algebra C Ps := i.toAlgebra
  let ε' : Ps := ⟨(0, TrivSqZeroExt.inr 1), by show residue C 0 = (0 : ResidueField C); simp⟩
  have hfin : Module.Finite C Ps := by
    classical
    refine ⟨⟨({1, ε'} : Finset Ps), eq_top_iff.2 fun x _ ↦ ?_⟩⟩
    obtain ⟨⟨a, y⟩, hx⟩ := x
    have hx' : residue C a = y.fst := hx
    obtain ⟨c, hc⟩ := residue_surjective (R := C) y.snd
    have : (⟨(a, y), hx⟩ : Ps) = a • (1 : Ps) + c • ε' := by
      rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one]
      refine Subtype.ext (Prod.ext ?_ ?_)
      · show a = a + c * 0
        ring
      · show y = TrivSqZeroExt.inl (residue C a) + TrivSqZeroExt.inl (residue C c) * TrivSqZeroExt.inr 1
        rw [TrivSqZeroExt.inl_mul_inr]
        ext
        · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hx']
        · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_inr,
            smul_eq_mul, _root_.mul_one, hc]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hart : IsArtinianRing Ps := IsArtinianRing.of_finite C Ps
  refine ⟨CommRingCat.of Ps, CommRingCat.ofHom i, CommRingCat.ofHom p, CommRingCat.ofHom σ, CommRingCat.ofHom q,
    by ext c; rfl, by ext c; exact RingHom.congr_fun hσi c, ?_, ?_, hloc, hart, fun c ↦ ⟨i c, rfl⟩, fun y ↦ ?_⟩
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      show Ideal.Quotient.mk _ x.1.1 = Ideal.Quotient.mk _ (x.1.1 + φ x.1.2.snd)
      refine (Ideal.Quotient.eq.2 ?_).symm
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      exact x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩
  · obtain ⟨a, ha⟩ := residue_surjective (R := C) y.fst
    exact ⟨⟨(a, y), ha⟩, rfl⟩

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem pull_ex {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre g n ζ s) :
    ∃ c' : SiegPre g n ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have hf' : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf, show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have H := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n B B ζ ζ (RingHom.id B) S S' s s' f rfl hf'
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem classified_of_small : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F C _ _ _ e he hme β c hc hcl
  set π := Ideal.Quotient.mk (Ideal.span {e}) with hπ
  obtain ⟨c₀, hc₀, -⟩ := pull_ex (s := spMap β) (s' := spMap (π.comp β)) (spMap π) (spMap_comp' β π).symm c
  obtain ⟨x₀, hx₀s, hx₀⟩ := hcl c₀ hc₀
  by_cases he0 : e = 0
  · have hker : ∀ a ∈ Ideal.span {e}, (RingHom.id C) a = 0 := by
      intro a ha
      rw [he0] at ha
      simpa using Ideal.mem_span_singleton.1 ha
    let ψ : C ⧸ Ideal.span {e} →+* C := Ideal.Quotient.lift _ (RingHom.id C) hker
    have hψπ : ψ.comp π = RingHom.id C := RingHom.ext fun a => by
      show ψ (π a) = a
      exact Ideal.Quotient.lift_mk _ _ _
    refine ⟨spMap ψ ≫ x₀, ?_, ?_⟩
    · rw [Category.assoc, hx₀s, ← spMap_comp', ← RingHom.comp_assoc, hψπ, RingHom.id_comp]
    · have h1 : SiegPB c c₀ (spMap ψ) := pb_cancel hc₀ (by
        rw [← spMap_comp', hψπ, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]; exact pb_id c)
      exact pb_comp hx₀ h1
  obtain ⟨x₁, hx₁s, hx₁⟩ := lift_lemma _ F.X F.s _ F.smooth C e (hme e he) β x₀ hx₀s
  obtain ⟨P, i, p, σ, q, hip, hiσ, sq1, sq2, hPl, hPa, hps, hqs⟩ := ring_lemma C e he hme he0
  let βP : CommRingCat.of (cycAway n) ⟶ P := CommRingCat.ofHom β ≫ i
  have hpβ : Spec.map p ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hip, Spec.map_id, Category.id_comp]
  have hσβ : Spec.map σ ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hiσ, Spec.map_id, Category.id_comp]
  let k := IsLocalRing.ResidueField C
  let β' : cycAway n →+* DualNumber k := (βP ≫ q).hom
  have hqβ : Spec.map q ≫ Spec.map βP = spMap β' := by
    rw [← Spec.map_comp]; rfl
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom π
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_ex (s' := Spec.map p ≫ Spec.map βP) x₁ (by rw [hx₁s, hpβ]) F.univ
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_ex (s' := Spec.map σ ≫ Spec.map βP) (𝟙 _) (by rw [Category.id_comp, hσβ]) c
  obtain ⟨c₀', hc₀', -⟩ := pull_ex (s' := Spec.map πC ≫ Spec.map p ≫ Spec.map βP) x₀
    (by rw [hx₀s, hpβ, spMap_comp']) F.univ
  have h01 : SiegPB c₀' c₁ (spMap π) := pb_cancel hc₁ (by rw [hx₁]; exact hc₀')
  have h0c : SiegPB c₀' c₀ (𝟙 _) := pb_cancel hx₀ (by rw [Category.id_comp]; exact hc₀')
  have h0c' : SiegPB c₀' c (spMap π) := by simpa using pb_comp hc₀ h0c
  have h02 : SiegPB c₀' c₂ (spMap π) := pb_cancel hc₂ (by rw [Category.comp_id]; exact h0c')
  obtain ⟨e', he'p, he'1, he'2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd P (CommRingCat.of C) (CommRingCat.of C)
    (CommRingCat.of (C ⧸ Ideal.span {e})) p σ πC πC sq1 hPl hPa Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective βP c₁ c₂ (hc₁p F.princ) (hc₂p hc) ⟨c₀', h01, h02⟩
  obtain ⟨eε, heε, heεp⟩ := pull_ex (s' := Spec.map q ≫ Spec.map βP) (Spec.map q) rfl e'
  obtain ⟨eε', heε', heε'p⟩ := pull_ex (s' := spMap β') (𝟙 _) (by rw [Category.id_comp, hqβ]) eε
  obtain ⟨v, hvs, hv₀⟩ := GlobalTheory.T.siegelObject_dualNumber_classified g n hg hn hodd F k β' eε' (heε'p (heεp he'p))
  have hεε : SiegPB eε eε' (𝟙 _) := pb_cancel heε' (by rw [Category.id_comp]; exact pb_id eε)
  have hv : SiegPB eε F.univ v := by simpa using pb_comp hv₀ hεε
  let ρ : CommRingCat.of C ⟶ CommRingCat.of k := CommRingCat.ofHom (IsLocalRing.residue C)
  let ε₀ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hw : Spec.map ρ ≫ Spec.map p = Spec.map ε₀ ≫ Spec.map q := by
    rw [← Spec.map_comp, ← Spec.map_comp, sq2.w]
  obtain ⟨ck, hck, -⟩ := pull_ex (s' := Spec.map ρ ≫ Spec.map p ≫ Spec.map βP) (Spec.map ρ) rfl c₁
  have hk1 : SiegPB ck F.univ (Spec.map ρ ≫ x₁) := pb_comp hc₁ hck
  have hk2 : SiegPB ck eε (Spec.map ε₀) := pb_cancel heε (by rw [← hw]; exact pb_comp he'1 hck)
  have hk3 : SiegPB ck F.univ (Spec.map ε₀ ≫ v) := pb_comp hv hk2
  have hglue : Spec.map ρ ≫ x₁ = Spec.map ε₀ ≫ v := by
    refine F.inj k _ _ _ ck ?_ hk1 hk3
    rw [Category.assoc, Category.assoc, hx₁s, hvs, ← hpβ, ← hqβ, ← Category.assoc, hw, Category.assoc]
  have hsq := GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique P (CommRingCat.of C) (CommRingCat.of (DualNumber k)) (CommRingCat.of k) p q ρ ε₀ sq2
    hPl hPa hps hqs inferInstance
  obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hsq F.X x₁ v hglue
  have hws : w ≫ F.s = Spec.map βP := by
    obtain ⟨w', -, hu⟩ := hsq (Sp (cycAway n)) (x₁ ≫ F.s) (v ≫ F.s) (by
      rw [← Category.assoc, hglue, Category.assoc])
    have a1 := hu (w ≫ F.s) ⟨by rw [← Category.assoc, hw1], by rw [← Category.assoc, hw2]⟩
    have a2 := hu (Spec.map βP) ⟨by rw [hpβ, hx₁s], by rw [hqβ, hvs]⟩
    rw [a1, a2]
  obtain ⟨e'', he'', he''p⟩ := pull_ex (s' := Spec.map βP) w hws F.univ
  have hq1 : SiegPB c₁ e'' (Spec.map p) := pb_cancel he'' (by rw [hw1]; exact hc₁)
  have hq2 : SiegPB eε e'' (Spec.map q) := pb_cancel he'' (by rw [hw2]; exact hv)
  have hiso : SiegPB e' e'' (𝟙 _) := GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n hn hodd P (CommRingCat.of C) (CommRingCat.of (DualNumber k))
    (CommRingCat.of k) p q ρ ε₀ sq2 hPl hPa IsLocalRing.residue_surjective (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)
    βP e'' e' c₁ eε (he''p F.princ) he'p hq1 he'1 hq2 heε
  refine ⟨Spec.map σ ≫ w, by rw [Category.assoc, hws, hσβ], ?_⟩
  have hcc2 : SiegPB c c₂ (𝟙 _) := pb_cancel hc₂ (by rw [Category.id_comp]; exact pb_id c)
  have := pb_comp he'' (pb_comp hiso (pb_comp he'2 hcc2))
  simpa using this

end GlobalTheory.SmallClassify
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmallStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegPB_lift_of_quotient_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SmallClassify.classified_of_small | exact GlobalTheory.SmallClassify.classified_of_small | (intros; apply GlobalTheory.SmallClassify.classified_of_small <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAnyField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAnyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegField

theorem classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  haveI : Module.FaithfullyFlat K (AlgebraicClosure K) := inferInstance
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F K (AlgebraicClosure K) β c hc fun c' hpb => ?_
  have hc' : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff _ _ _).2 hpb) hc
  exact GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F (AlgebraicClosure K) ((algebraMap K (AlgebraicClosure K)).comp β) c' hc'

end GlobalTheory.SiegField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAnyFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_classifies_principal_any_field : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegField.classify | exact GlobalTheory.SiegField.classify | (intros; apply GlobalTheory.SiegField.classify <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelArtin

theorem exists_socle (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (hm : IsLocalRing.maximalIdeal C ≠ ⊥) :
    ∃ e : C, e ≠ 0 ∧ e ∈ IsLocalRing.maximalIdeal C ∧ ∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0 := by
  set m := IsLocalRing.maximalIdeal C
  have hnil : IsNilpotent m := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hex : ∃ k, m ^ k = ⊥ := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hk]; rfl⟩
  classical
  let k := Nat.find hex
  have hk : m ^ k = ⊥ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : m ^ k = ⊤ := by rw [h0, pow_zero, Ideal.one_eq_top]
    rw [this] at hk
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp (hk ▸ bot_le))
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hk
    exact hm hk
  have hprev : m ^ (k - 1) ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  refine ⟨e, he0, ?_, ?_⟩
  · exact Ideal.pow_le_self (by omega) he
  · intro a ha
    have : a * e ∈ m ^ k := by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk', pow_succ']
      exact Ideal.mul_mem_mul ha he
    rw [hk] at this
    simpa using this

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F
  suffices H : ∀ (N : ℕ) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C],
      Module.length C C = N → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)),
      c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f by
    intro C _ _ _ β c hc
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top (R := C) (M := C))
    exact H N C hN.symm β c hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C _ _ _ hN β c hc
  by_cases hm : IsLocalRing.maximalIdeal C = ⊥
  · letI : Field C := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    exact GlobalTheory.T.siegel_family_classifies_principal_any_field g n hg hn hodd F C β c hc
  obtain ⟨e, he0, hem, hann⟩ := exists_socle C hm
  set I : Ideal C := Ideal.span {e}
  have hIt : I ≠ ⊤ := by
    intro h
    have : I ≤ IsLocalRing.maximalIdeal C := (Ideal.span_singleton_le_iff_mem _).mpr hem
    rw [h] at this
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (C ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hlenQ : Module.length C (C ⧸ I) = Module.length (C ⧸ I) (C ⧸ I) :=
    Module.length_eq_of_surjective (R := C ⧸ I) (S := C) (M := C ⧸ I) Ideal.Quotient.mk_surjective
  have hsum : Module.length C C = Module.length C I + Module.length C (C ⧸ I) :=
    Module.length_eq_add_of_exact I.subtype I.mkQ I.injective_subtype I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I)
  haveI : Nontrivial I := ⟨⟨⟨e, Ideal.subset_span rfl⟩, 0, fun h => he0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.length C I := Module.length_pos
  rw [hN, hlenQ] at hsum
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (show Module.length C I ≠ ⊤ from fun h => by
    rw [h, top_add] at hsum; exact ENat.natCast_ne_top _ hsum)
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (show Module.length (C ⧸ I) (C ⧸ I) ≠ ⊤ from fun h => by
    rw [h, add_top] at hsum; exact ENat.natCast_ne_top _ hsum)
  rw [← hb, ← hM] at hsum
  rw [← hb] at hpos
  have hb0 : 0 < b := by exact_mod_cast hpos
  have hNM : N = b + M := by exact_mod_cast hsum
  have hlt : M < N := by omega
  refine GlobalTheory.T.exists_siegPB_lift_of_quotient_lift g n hg hn hodd F C e hem hann β c hc ?_
  intro c₀ hpb
  have hcomm : spMap (Ideal.Quotient.mk I) ≫ spMap β = spMap ((Ideal.Quotient.mk I).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hc₀ : c₀.Principal :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp C) (Sp (C ⧸ I)) (spMap β)
      (spMap ((Ideal.Quotient.mk I).comp β)) (spMap (Ideal.Quotient.mk I)) c hcomm).2 c₀ hpb hc
  exact ih M hlt (C ⧸ I) hM.symm _ c₀ hc₀

end GlobalTheory.SiegelArtin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_point_lifts_to_artinian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelArtin.main | exact GlobalTheory.SiegelArtin.main | (intros; apply GlobalTheory.SiegelArtin.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFormalAssemble

theorem siegPB_id_of_tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  intro g n B _ ζ R _ _ I hI s s' c c' t ce φ ψ β hc hφ hψ hβφ hβψ
  have H := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  have hp : GlobalTheory.AbLaw.IsProjBy c.A.hom :=
    GlobalTheory.WtTower.isProjBy_of_relAmple c.A (pull_isLB c.isLB _) hc.1
  obtain ⟨G, hG, hGφ, -, -, hGP⟩ := GlobalTheory.AlgUniq.exists_iso_algebraisation H R I hI (fun e => (ce e).A) β c.A c'.A
    c.ab c'.ab hp φ ψ (fun e => (hφ e).1) hβφ (fun e => (hψ e).1) hβψ
  choose b₂ hb₂ hb₂P using fun e => (hφ e).2.1
  choose b₂' hb₂' hb₂'P using fun e => (hψ e).2.1
  have hP := hGP c.P c'.P b₂ b₂' c.isLB c'.isLB hb₂ hb₂' fun e =>
    LBIso.trans (pull_isLB c.isLB _) (ce e).isLB (pull_isLB c'.isLB _) (LBIso.symm (hb₂P e)) (hb₂'P e)
  refine ⟨G.hom.left, (G.hom ⊗ₘ G.hom).left, isGrpPullback_of_iso G, ⟨?_, ?_⟩, hP, fun a => ?_⟩
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
  · have : IsProper c'.A.hom := c'.ab.proper
    have : IsProper (𝟙_ (Over (Sp R))).hom := show IsProper (𝟙 _) from inferInstance
    have key : c.lev a ≫ G.hom = c'.lev a := by
      refine GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext H hI fun e => ?_
      have hw : pullback.fst (𝟙_ (Over (Sp R))).hom (Out.thick R I e) =
          pullback.snd (𝟙_ (Over (Sp R))).hom (Out.thick R I e) ≫ Out.thick R I e := by
        rw [← pullback.condition]; exact (Category.comp_id _).symm
      have l1 := (hφ e).2.2 a
      have l2 := (hψ e).2.2 a
      simp only [pow_one] at l1 l2
      rw [hw, Over.comp_left, Category.assoc, Category.assoc, ← reassoc_of% l1, ← l2, ← hGφ e]
    rw [Category.id_comp, ← key, Over.comp_left]

end GlobalTheory.SiegFormalAssemble
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  first | exact @GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower | exact GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower | (intros; apply GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickenings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickenings
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LocalThickGlue

theorem subsingleton_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) =
        IsLocalRing.maximalIdeal R := by
    intro P
    have hP : (P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : IsLocalRing.maximalIdeal R ^ (e + 1) ≤
        P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact P.asIdeal.zero_mem
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm
  constructor
  intro P Q
  ext1
  exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ((key P).trans (key Q).symm)

theorem pow_succ_ne_top (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing.maximalIdeal R ^ (e + 1) ≠ ⊤ := fun h =>
  (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))

theorem exists_glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X),
    (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) →
    ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  intro R _ _ hc X x hx
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hc
  haveI hnt : ∀ e, Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top R e)
  haveI hss := subsingleton_primeSpectrum R
  let z : ∀ e, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    (Classical.arbitrary (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))))
  have hpt : ∀ e (a : Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))), x e a = x 0 (z 0) := by
    intro e
    induction e with
    | zero => intro a; rw [Subsingleton.elim (α := PrimeSpectrum _) a (z 0)]
    | succ n ih =>
      intro a
      rw [Subsingleton.elim (α := PrimeSpectrum _) a (Out.thickTrans R (IsLocalRing.maximalIdeal R) n (z n))]
      have e1 := congrArg (fun h => h (z n)) (hx n)
      simp only [Scheme.Hom.comp_apply] at e1
      rw [e1, ih]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x 0 (z 0) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : ∀ e, Set.range (x e) ⊆ Set.range hU'.fromSpec := by
    intro e
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt e a]
    exact hqU
  let ρ : ∀ e, Γ(X, U) ⟶ CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Spec.preimage (IsOpenImmersion.lift hU'.fromSpec (x e) (hr e))
  have hρ : ∀ e, Spec.map (ρ e) ≫ hU'.fromSpec = x e := fun e => by
    simp only [ρ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ e, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))).comp (ρ (e + 1)).hom =
      (ρ e).hom := fun e => by
    have h1 : ρ (e + 1) ≫ CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) =
        ρ e := by
      apply Spec.map_injective
      rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Category.assoc, hρ, hρ]
      exact hx e
    exact congrArg CommRingCat.Hom.hom h1
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  let F : Γ(X, U) →+* R := IsAdicComplete.StrictMono.liftRingHom (IsLocalRing.maximalIdeal R) ha
    (fun n => (ρ n).hom) (fun {n} => hcomp n)
  refine ⟨Spec.map (CommRingCat.ofHom F) ≫ hU'.fromSpec, fun e => ?_⟩
  have hF : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))).comp F = (ρ e).hom :=
    IsAdicComplete.StrictMono.mk_comp_liftRingHom (IsLocalRing.maximalIdeal R) ha _ _
  rw [← hρ e, ← Category.assoc]
  congr 1
  rw [Out.thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hF]
  rfl

end GlobalTheory.LocalThickGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickeningsStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  first | exact @GlobalTheory.LocalThickGlue.exists_glue | exact GlobalTheory.LocalThickGlue.exists_glue | (intros; apply GlobalTheory.LocalThickGlue.exists_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SFamCompl

theorem glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e :=
  GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings

theorem ext_affine : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (A : Type) [CommRing A]
    (f f' : Sp R ⟶ Sp A), (∀ e, Out.thick R I e ≫ f = Out.thick R I e ≫ f') → f = f' := by
  intro R _ I hI A _ f f' h
  rw [← Spec.map_preimage f, ← Spec.map_preimage f']
  congr 1
  ext a
  refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_
  cases k with
  | zero =>
    rw [SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
    trivial
  | succ e =>
    have he := h e
    rw [← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp] at he
    have he' := congrArg (fun q => q.hom a) (Spec.map_injective he)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'
    rw [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 he'

theorem srel_comp {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
    {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · rw [pow_one, pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] (I : Ideal R) (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s) (c' : SiegPre g n (b.ζ : B) s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n (b.ζ : B) (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left), 3 ≤ n → Odd n → c.Principal → c'.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → ∃ β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left, ∀ e, β e ≫ φ (e + 1) = φ e ∧ β e ≫ ψ (e + 1) = ψ e := by
  intro g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  have key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e) :=
      GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩)
        (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)
    obtain ⟨β, hβ⟩ := (sRel_one_one_iff _ _ _).2 h1
    refine ⟨β, ?_, ?_⟩
    · have := srel_comp (hφ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)
    · have := srel_comp (hψ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)
  choose β hβ using key
  exact ⟨β, hβ⟩

theorem assemble : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) :=
  GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic

theorem alg : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), IsAdicComplete I R → 3 ≤ n → Odd n → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s)
    (c' : SiegPre g n (b.ζ : B) s'), c.Principal → c'.Principal →
    (∀ e, ∃ (t : Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : SiegPre g n (b.ζ : B) t),
      SiegPB ce c (Out.thick R I e) ∧ SiegPB ce c' (Out.thick R I e)) → SiegPB c c' (𝟙 _) := by
  intro g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h
  choose t ce hce hce' using h
  choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)
  choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)
  obtain ⟨β, hβ⟩ := tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  exact assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)

theorem quot_local (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem quot_artin {R : Type} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m.IsMaximal)
    (N : ℕ) : IsArtinianRing (R ⧸ m ^ (N + 1)) := by
  have : Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1)) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    have hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := hp.le_of_pow_le h1
    have h3 := hm.eq_of_le hp.ne_top h2
    have h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal := h3 ▸ hm
    have h5 := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1)))
      Ideal.Quotient.mk_surjective h4
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h5
    exact h5.resolve_left hP.ne_top
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_ {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

end GlobalTheory.SFamCompl

namespace GlobalTheory.SFamCompl

theorem classified_of_complete : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ hR β c hc
  have hn0 : n ≠ 0 := by omega
  set m := IsLocalRing.maximalIdeal R with hm
  haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e
  haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e
  let βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1)) := fun e => (Ideal.Quotient.mk _).comp β
  have hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n)) := by
    intro e
    rw [spMap_id_, Category.comp_id]
    exact (spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm
  have hpull := fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)
  choose ce hce using fun e => (hpull e).1 c
  have hcep : ∀ e, (ce e).Principal := fun e => (hpull e).2.1 c (ce e) (hce e) hc
  choose x hxs hxpb using fun e => GlobalTheory.T.siegel_point_lifts_to_artinian g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)
  have hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e) :=
      GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e)
      (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)
    rw [Category.assoc, hxs (e + 1)]
    exact (spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))
  obtain ⟨f, hf⟩ := glue R hR F.X x hcomp
  have hfs : f ≫ F.s = spMap β := by
    refine ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_
    rw [← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]
  have hpf := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])
  obtain ⟨c', hc'⟩ := hpf.1 F.univ
  have hc'p : c'.Principal := hpf.2.1 F.univ c' hc' F.princ
  have key : SiegPB c c' (𝟙 _) := by
    refine alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_
    refine ⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩
    rw [hf e]
    exact hxpb e
  refine ⟨f, hfs, ?_⟩
  simpa using GlobalTheory.SiegelPullComp.pb_comp hc' key

end GlobalTheory.SFamCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classifies_complete_noetherian_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SFamCompl.classified_of_complete | exact GlobalTheory.SFamCompl.classified_of_complete | (intros; apply GlobalTheory.SFamCompl.classified_of_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFamLocal

theorem exists_point_of_principal : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ β c hc
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  haveI : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F R (AdicCompletion (IsLocalRing.maximalIdeal R) R) β c hc ?_
  intro c' hc'
  have hp : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff c' c _).2 hc') hc
  exact GlobalTheory.T.siegelFamily_classifies_complete_noetherian_local g n hg hn hodd F (AdicCompletion (IsLocalRing.maximalIdeal R) R) inferInstance
    ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp β) c' hp

end GlobalTheory.SiegelFamLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classifies_noetherian_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelFamLocal.exists_point_of_principal | exact GlobalTheory.SiegelFamLocal.exists_point_of_principal | (intros; apply GlobalTheory.SiegelFamLocal.exists_point_of_principal <;> assumption)
end
