module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InversionOfAdjunctionProj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombination
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_ordQ_eq_ord_div : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ),
    φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  intro k K _ _ c φ
  induction φ using Finsupp.induction with
  | zero => intro _; exact ⟨1, 1, one_pos, fun E => by simp⟩
  | single_add a b f ha hb ih =>
    intro h0
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h0
      exact hb h0
    have hf0 : f 0 = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha0), zero_add] at h0
      exact h0
    obtain ⟨m, g, hm, hg⟩ := ih hf0
    refine ⟨m * b.den, g ^ b.den * (Units.mk0 a ha0) ^ (b.num * m), ?_, fun E => ?_⟩
    · exact Nat.mul_pos hm b.pos
    · have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [map_add (f := _), Place.ordQ_single, hg E, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, E.ord_mul (pow_ne_zero _ g.ne_zero)
          (zpow_ne_zero _ (Units.mk0 a ha0).ne_zero), E.ord_pow, E.ord_zpow, Units.val_mk0]
      push_cast
      rw [← Rat.mul_den_eq_num b]
      field_simp
      ring

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombinationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ), φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  first | exact @GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | exact GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | (intros; apply GlobalTheory.FieldPair.exists_ordQ_eq_ord_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpec
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.OpenSpecField

variable {S : Type} [CommRing S] [IsDomain S] {Y : Scheme.{0}} [IsIntegral Y]
  (j : Sp S ⟶ Y) [IsOpenImmersion j]

abbrev img : Y.Opens := j ''ᵁ ⊤

theorem isAffineOpen_img : IsAffineOpen (img j) := (isAffineOpen_top _).image_of_isOpenImmersion j

theorem mem_img (q : Sp S) : j.base q ∈ img j := ⟨q, trivial, rfl⟩

instance : Nonempty (img j) := ⟨⟨_, mem_img j (Classical.arbitrary (PrimeSpectrum S))⟩⟩

theorem gen_mem_img : genericPoint Y ∈ img j :=
  gen_mem (mem_img j (Classical.arbitrary (PrimeSpectrum S)))

def secEquiv : Γ(Y, img j) ≃+* S :=
  ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv

instance : IsFractionRing Γ(Y, img j) Y.functionField :=
  functionField_isFractionRing_of_isAffineOpen Y _ (isAffineOpen_img j)

def fieldEquiv : Y.functionField ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv (secEquiv j)

theorem fieldEquiv_fnOf (a : Γ(Y, img j)) :
    fieldEquiv j (fnOf _ (gen_mem_img j) a) = algebraMap S (FractionRing S) (secEquiv j a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem mem_basicOpen_iff (q : Sp S) (b : Γ(Y, img j)) :
    j.base q ∈ Y.basicOpen b ↔ secEquiv j b ∉ q.asIdeal := by
  have h : (Sp S).basicOpen ((j.appIso ⊤).hom b) = (Sp S).basicOpen (j.app (img j) b) := by
    rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  change q ∈ j ⁻¹ᵁ Y.basicOpen b ↔ _
  rw [Scheme.preimage_basicOpen, ← h, basicOpen_eq_of_affine']
  exact PrimeSpectrum.mem_basicOpen _ _

theorem secEquiv_algX [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S)) (a : ℂ) :
    secEquiv j (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (img j) a) = algebraMap ℂ S a := by
  have key : p.appLE ⊤ (img j) (show img j ≤ p ⁻¹ᵁ ⊤ from le_top) ≫ (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ CommRingCat.ofHom (algebraMap ℂ S) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    simp only [hjp]
    have e : (spMap (algebraMap ℂ S)).appLE ⊤ ⊤ (show (⊤ : (Sp S).Opens) ≤ spMap (algebraMap ℂ S) ⁻¹ᵁ ⊤ from le_top) = (spMap (algebraMap ℂ S)).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv a)) key
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp

theorem fieldEquiv_constFn [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S))
    (a : ℂ) : fieldEquiv j (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a := by
  rw [← fnOf_comp_algX p (img j) (gen_mem_img j), RingHom.comp_apply, fieldEquiv_fnOf,
    secEquiv_algX j p hjp, IsScalarTower.algebraMap_apply ℂ S (FractionRing S)]

theorem mem_map_locRing (q : Sp S) (g : FractionRing S) :
    g ∈ (locRing (j.base q)).map (fieldEquiv j).toRingHom ↔
      ∃ a b : S, b ∉ q.asIdeal ∧
        g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  have hU := isAffineOpen_img j
  have hy := mem_img j q
  have hg := gen_mem_img j
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨V, hyV, c, rfl⟩ := (mem_locRing.1 hf).exists_fnOf
    obtain ⟨b, hbV, hyb⟩ := hU.exists_basicOpen_le ⟨_, hyV⟩ hy
    have := hU.isLocalization_basicOpen b
    obtain ⟨⟨t, s, hs⟩, hts⟩ := IsLocalization.surj (Submonoid.powers b) (resG Y hbV c)
    obtain ⟨n, rfl⟩ := hs
    have hW : genericPoint Y ∈ Y.basicOpen b := gen_mem hyb
    have e1 := congrArg (fnOf _ hW) hts
    change fnOf _ hW (resG Y hbV c * resG Y (Y.basicOpen_le b) (b ^ n)) =
      fnOf _ hW (resG Y (Y.basicOpen_le b) t) at e1
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e1
    refine ⟨secEquiv j t, secEquiv j (b ^ n), ?_, ?_⟩
    · rw [map_pow]
      exact fun h => (mem_basicOpen_iff j q b).1 hyb (q.isPrime.mem_of_pow_mem n h)
    · rw [← fieldEquiv_fnOf, ← fieldEquiv_fnOf]
      change fieldEquiv j _ * _ = _
      rw [← map_mul, e1]
  · rintro ⟨a, b, hb, e⟩
    let a' := (secEquiv j).symm a
    let b' := (secEquiv j).symm b
    have hb' : j.base q ∈ Y.basicOpen b' :=
      (mem_basicOpen_iff j q b').2 (by simpa [b'] using hb)
    refine ⟨fnOf _ hg a' * (fnOf _ hg b')⁻¹, ?_, ?_⟩
    · exact mem_locRing.2 ((regAt_fnOf hy hg a').mul
        ((unitAt_fnOf_iff hy hg b').2 hb').inv.regAt)
    · have hb0 : algebraMap S (FractionRing S) b ≠ 0 := by
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
        rintro rfl
        exact hb q.asIdeal.zero_mem
      change fieldEquiv j _ = g
      rw [map_mul, map_inv₀, fieldEquiv_fnOf, fieldEquiv_fnOf]
      simp only [a', b', RingEquiv.apply_symm_apply]
      rw [← e, mul_inv_cancel_right₀ hb0]

theorem exists_fieldEquiv (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0})
    [IsIntegral Y] (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j]
    (hjp : j ≫ p = spMap (algebraMap ℂ S)) :
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧
          g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a :=
  ⟨fieldEquiv j, fieldEquiv_constFn j p hjp, mem_map_locRing j⟩

end GlobalTheory.OpenSpecField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpecStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j], j ≫ p = spMap (algebraMap ℂ S) →
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧ g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  first | exact @GlobalTheory.OpenSpecField.exists_fieldEquiv | exact GlobalTheory.OpenSpecField.exists_fieldEquiv | (intros; apply GlobalTheory.OpenSpecField.exists_fieldEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionField
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem IsLocModel.exists_finiteType_localization :
    ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  intro L _ c R hR
  letI := hR.isLocalRing
  letI : Algebra ℂ R := (c.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  set A := Algebra.adjoin ℂ (σ : Set R) with hA
  let S : Subring L := A.toSubring.map R.subtype
  have hSR : S ≤ R := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have memS : ∀ x : R, x ∈ A → (x : L) ∈ S := fun x hx => ⟨x, hx, rfl⟩
  have hS : ∀ a, c a ∈ S := fun a => memS ⟨c a, hR.const_mem a⟩ (A.algebraMap_mem a)
  let q : Ideal S := (IsLocalRing.maximalIdeal R).comap (Subring.inclusion hSR)
  have unit_ne : ∀ t : R, IsUnit t → (t : L) ≠ 0 := by
    intro t ht h0
    obtain ⟨u, hu⟩ := ht.exists_right_inv
    have := congrArg (fun x : R => (x : L)) hu
    simp [h0] at this
  refine ⟨S, hS, q, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · have hA' : Algebra.FiniteType ℂ A :=
      (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset σ)
    let e : A.toSubring ≃+* S := A.toSubring.equivMapOfInjective R.subtype Subtype.val_injective
    have he : c.codRestrict S hS = (e.toRingHom : A →+* S).comp (algebraMap ℂ A) := by
      ext a; rfl
    have h2 : (algebraMap ℂ A).FiniteType := RingHom.finiteType_algebraMap.mpr hA'
    rw [he]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.surjective) h2
  · intro f
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hR.frac f
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    refine ⟨r1 * t1 * t2, ?_, r2 * t2 * t1, ?_, ?_, ?_⟩
    · simpa using memS _ (A.mul_mem h1 ht2A)
    · simpa using memS _ (A.mul_mem h2 ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring
  · intro f
    constructor
    · intro hf
      obtain ⟨t, htA, ht, h⟩ := hσ ⟨f, hf⟩
      refine ⟨⟨_, memS _ h⟩, ⟨_, memS _ htA⟩, ?_, rfl⟩
      intro hq
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · rintro ⟨a, b, hb, e⟩
      have hu : IsUnit (Subring.inclusion hSR b) := by
        by_contra h; exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu'⟩ := hu.exists_right_inv
      have hu'' : (b : L) * (u : L) = 1 := by
        have := congrArg (fun x : R => (x : L)) hu'; simpa using this
      have hf : f = a * u := by rw [← e, mul_assoc, hu'', mul_one]
      rw [hf]; exact R.mul_mem (hSR a.2) u.2

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_localization_same_fractionField : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | exact GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | (intros; apply GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoi
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocModelProj


open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw in
theorem exists_projective_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y),
      IsProjOver p ∧ IsOpenImmersion j ∧ LocallyOfFiniteType p ∧ j ≫ p = spMap (algebraMap ℂ S) := by
  have : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))
  have := isProper_str ℂ N
  exact ⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩,
    inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩

theorem topologicalKrullDim_eq_of_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] (j : Sp S ⟶ Y) [IsOpenImmersion j] (n : ℕ) (h : Algebra.trdeg ℂ S = n) :
    topologicalKrullDim Y = n := by
  have : Nonempty (Sp S) := inferInstance
  rw [← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]
  change topologicalKrullDim (PrimeSpectrum S) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]

theorem exists_projective_of_isLocModel : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  intro L _ c R n x hR hx
  obtain ⟨S, hS, q, hq, hft, hfrac, hmem⟩ := GlobalTheory.T.exists_finiteType_localization_same_fractionField L c R hR
  letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra
  letI : Algebra S L := S.subtype.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℂ S := hft
  haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun f => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  have htr : Algebra.trdeg ℂ S = n := by
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
    rw [← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero] at h2
    rw [← h2, Cardinal.mk_fin]
  obtain ⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩ := exists_projective_openImmersion S
  obtain ⟨e, hc, hloc⟩ := GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp
  let e2 : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  refine ⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩
  · change e2 (e (GlobalTheory.Cartier.constFn p a)) = c a
    rw [hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]
    rfl
  · ext g
    have h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔
        e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by simp⟩
      · rintro ⟨u, hu, hu'⟩
        refine ⟨u, hu, ?_⟩
        change e2 (e u) = g
        rw [show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]
    rw [h1, hloc ⟨q, hq⟩, hmem g]
    refine exists₂_congr fun a b => and_congr_right fun _ => ?_
    constructor
    · intro h
      have := congrArg e2 h
      rwa [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes] at this
    · intro h
      apply e2.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
      exact h

end GlobalTheory.LocModelProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  first | exact @GlobalTheory.LocModelProj.exists_projective_of_isLocModel | exact GlobalTheory.LocModelProj.exists_projective_of_isLocModel | (intros; apply GlobalTheory.LocModelProj.exists_projective_of_isLocModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModel
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

section Transport

variable {k K K' : Type} [Field k] [Field K] [Field K'] {c : k →+* K} {c' : k →+* K'}

theorem Place.contains_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (R : Subring K) :
    E'.Contains (R.map e.toRingHom) ↔ E.Contains R := by
  constructor
  · intro h f hf
    exact (hring f).1 (h _ ⟨f, hf, rfl⟩)
  · rintro h _ ⟨f, hf, rfl⟩
    exact (hring f).2 (h f hf)

theorem Place.isPrimeOf_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (hord : ∀ a, E'.ord (e a) = E.ord a)
    (R : Subring K) : E'.IsPrimeOf (R.map e.toRingHom) ↔ E.IsPrimeOf R := by
  rw [Place.IsPrimeOf, Place.IsPrimeOf, Place.contains_map_iff e E E' hring]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f' hf' => ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hb0, hbo, hfb⟩ := h (e f) ((hring f).2 hf)
    refine ⟨a, ha, b, hb, fun h0 => hb0 (by simp [h0]), (hord b).symm.trans hbo, e.injective ?_⟩
    simpa using hfb
  · obtain ⟨a, ha, b, hb, hb0, hbo, hfb⟩ := h (e.symm f') ((hring _).1 (by simpa using hf'))
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simpa using hb0, (hord b).trans hbo, ?_⟩
    rw [← hfb]
    simp

theorem adjKlt_congr {n : ℕ} {T : Subring K} {S : Place c} {η : Forms c n} {φ ψ : K →₀ ℚ}
    (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (h : ∀ P : Place c, P.ordQ φ = P.ordQ ψ) : AdjKlt c n T S η φ ↔ AdjKlt c n T S η ψ := by
  have h' : ∀ P : Place c, P.disc η φ = P.disc η ψ := fun P => by rw [Place.disc, Place.disc, h]
  simp only [AdjKlt, h', hφ, hψ]

end Transport

theorem klt_of_adjKlt_locModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L)
    (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T →
    IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 →
    S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ →
    AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  intro hP L _ c n T x φ f S hT hTic hx hfT hf0 hS hSf hSd hEff hAdj
  obtain ⟨Y, hY, p, e, y, hproj, hdim, hc, hy⟩ := GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint L c T n x hT hx
  haveI := hY
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ Y p hproj
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hc' : ∀ a, e.symm (c a) = Cartier.constFn p a := fun a => by
    rw [← hc a]
    exact e.symm_apply_apply _
  have hyT : T.map e.symm.toRingHom = locRing y := by
    rw [← hy]
    ext z
    simp [Subring.mem_map]
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants c (Cartier.constFn p) e.symm hc'
  obtain ⟨hx', -, -, -⟩ := GlobalTheory.T.ringEquiv_transports_varietyPair_data c (Cartier.constFn p) e.symm hc' n x T φ hx
  have hψ0 : (φ + Finsupp.single f 1 : L →₀ ℚ) 0 = 0 := by
    simp [hEff.apply_zero, Finsupp.single_apply, hf0]
  obtain ⟨m, g, hm, hg⟩ := GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination (Cartier.constFn p)
    (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) (by
      rw [← map_zero e.symm, Finsupp.mapDomain_apply_of_injective e.symm.injective]
      exact hψ0)

  have hkey : ∀ E : Place c, (Φ E).disc (dForm (Cartier.constFn p) (e.symm ∘ x))
      (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      E.disc (dForm c x) (φ + Finsupp.single f 1) := fun E => by
    rw [Place.disc, Place.disc, (hΦ E).2.2.1, (hΦ E).2.2.2 n x hx]
    rfl
  have hψ : ∀ E : Place c, E.disc (dForm c x) (φ + Finsupp.single f 1) =
      E.disc (dForm c x) φ - E.ord f := fun E => by
    simp only [Place.disc, map_add (f := _), Place.ordQ_single]
    ring
  have hordQ : ∀ P : Place (Cartier.constFn p),
      P.ordQ (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      P.ordQ (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := fun P => by
    rw [hg, Place.ordQ_single]
    ring
  have hdisc : ∀ D : DivOver p, discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g =
      (Φ.symm (placeEquiv p D)).disc (dForm c x) (φ + Finsupp.single f 1) := fun D => by
    rw [← disc_placeEquiv, ← hkey, Φ.apply_symm_apply, Place.disc, Place.disc, hordQ]
  let f' : Y.functionFieldˣ := Units.mk0 (e.symm f) (by simpa using hf0)
  have hord : ∀ D : DivOver p, (D.ord f' : ℚ) = (Φ.symm (placeEquiv p D)).ord f := fun D => by
    rw [← ord_placeEquiv]
    have h := (hΦ (Φ.symm (placeEquiv p D))).2.1 f
    rw [Φ.apply_symm_apply] at h
    exact_mod_cast h

  have hstalk : IsIntegrallyClosed (Y.presheaf.stalk y) := by
    let e₁ : Y.presheaf.stalk y ≃+* locRing y := RingEquiv.ofBijective
      (algebraMap (Y.presheaf.stalk y) Y.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
    have : IsIntegrallyClosed (locRing y) := IsIntegrallyClosed.of_equiv
      ((T.equivMapOfInjective e.symm.toRingHom e.symm.injective).trans
        (RingEquiv.subringCongr hyT))
    exact IsIntegrallyClosed.of_equiv e₁.symm
  have hreg : RegAt y (f' : Y.functionField) := by
    rw [← mem_locRing, ← hyT]
    exact ⟨f, hfT, rfl⟩
  have hSprime : (placeEquiv p ((placeEquiv p).symm (Φ S))).IsPrimeOf (locRing y) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    exact (Place.isPrimeOf_map_iff e.symm S (Φ S) (hΦ S).1 (hΦ S).2.1 T).2 hS
  have hSord : ((placeEquiv p).symm (Φ S)).ord f' = 1 := by
    have h := hord ((placeEquiv p).symm (Φ S))
    rw [Equiv.apply_symm_apply, Φ.symm_apply_apply, hSf] at h
    exact_mod_cast h
  have hSdisc : discrep ((placeEquiv p).symm (Φ S)) (dForm (Cartier.constFn p) (e.symm ∘ x)) m g
      = -1 := by
    rw [hdisc, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ, hSd, hSf]
    norm_num
  have heff : ∀ D : DivOver p, (placeEquiv p D).IsPrimeOf (locRing y) →
      discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g ≤ 0 := by
    intro D hD
    have hE : (Φ.symm (placeEquiv p D)).IsPrimeOf T := by
      refine (Place.isPrimeOf_map_iff e.symm _ (Φ (Φ.symm (placeEquiv p D)))
        (hΦ _).1 (hΦ _).2.1 T).1 ?_
      rw [Φ.apply_symm_apply, hyT]
      exact hD
    have h0 : (0 : ℚ) ≤ (Φ.symm (placeEquiv p D)).ord f := by
      exact_mod_cast ((Φ.symm (placeEquiv p D)).ord_nonneg_iff hf0).2 (hE.1 f hfT)
    rw [hdisc, hψ]
    linarith [hEff.disc_le hE]
  have hadj : AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p ((placeEquiv p).symm (Φ S)))
      (dForm (Cartier.constFn p) (e.symm ∘ x)) (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    have h := GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv c (Cartier.constFn p) e.symm hc' n x T _ S (Φ S) hx (hΦ S).1 hAdj
    exact (adjKlt_congr h.apply_zero (Finsupp.single_eq_of_ne g.ne_zero.symm) hordQ).1 h
  have hmain := GlobalTheory.T.inversion_of_adjunction_proj_alt hP Y p n hproj hdim (e.symm ∘ x) m g f' y ((placeEquiv p).symm (Φ S))
    hx' hm hstalk hreg hSprime hSord hSdisc heff hadj
  refine ⟨hEff.form_ne_zero, hEff.apply_zero, fun E hE => ?_⟩
  have hThr : ((placeEquiv p).symm (Φ E)).Through y := by
    rw [← contains_placeEquiv, Equiv.apply_symm_apply, ← hyT]
    exact (Place.contains_map_iff e.symm E (Φ E) (hΦ E).1 T).2 hE
  have h := hmain _ hThr
  rw [hdisc, hord, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ] at h
  linarith

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.klt_of_adjunctionKlt_localModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L) (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T → IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 → S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ → AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.klt_of_adjKlt_locModel | exact GlobalTheory.FieldPair.klt_of_adjKlt_locModel | (intros; apply GlobalTheory.FieldPair.klt_of_adjKlt_locModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModel
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PrimeElementPlace

theorem main : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  intro L K _ _ cL cK n T hT ψ f _ hc hker hf hR
  classical
  haveI hfr : IsFractionRing T L := IsFractionRing.of_field T L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hT.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let A : Subalgebra T L :=
    Localization.subalgebra.ofField L (RingHom.ker ψ).primeCompl (RingHom.ker ψ).primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime A (RingHom.ker ψ) := (inferInstance : IsLocalization (RingHom.ker ψ).primeCompl A)
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (RingHom.ker ψ)
  letI : Algebra ℂ T := (cL.codRestrict T hT.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T := hT.essFiniteType
  haveI : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing ℂ T
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ψ).primeCompl A inferInstance
  have hinjA : Function.Injective (algebraMap T A) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A => (z : L)) h)
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap T A f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ψ) A, hker, Ideal.map_span,
      Set.image_singleton]
  have hf' : algebraMap T A f ≠ 0 := fun h => hf (hinjA (h.trans (map_zero _).symm))
  have hprinc : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsPrincipalIdealRing A :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := A)).out 1 5).2 hprinc
  haveI hdvrA : IsDiscreteValuationRing A := by
    refine ⟨?_⟩
    rw [hmax]
    intro h
    exact hf' ((Ideal.span_singleton_eq_bot).1 h)
  have hval : ∀ x : L, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring := fun x => by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left; rw [← hy]; exact y.2
    · right; rw [← hy]; exact y.2
  let V : ValuationSubring L := ValuationSubring.ofSubring A.toSubring hval
  let e : A ≃+* V :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  have hTA : ∀ t : L, t ∈ T → t ∈ V := fun t ht => A.algebraMap_mem (⟨t, ht⟩ : T)
  have hcV : ∀ a, cL a ∈ V := fun a => hTA _ (hT.const_mem a)
  have heft : (cL.codRestrict V hcV).EssFiniteType := by
    have h2 : (algebraMap T A).EssFiniteType := RingHom.essFiniteType_algebraMap.2
      (Algebra.EssFiniteType.of_isLocalization A (RingHom.ker ψ).primeCompl)
    have h3 := (hT.essFiniteType.comp h2).comp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    have e' : e.toRingHom.comp ((algebraMap T A).comp (cL.codRestrict T hT.const_mem)) =
        cL.codRestrict V hcV := RingHom.ext fun a => Subtype.ext rfl
    exact e' ▸ h3
  let S : Place cL := ⟨V, hcV, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, heft⟩
  have hS : S.IsPrimeOf T := by
    refine ⟨fun t ht => hTA t ht, fun x hx => ?_⟩
    obtain ⟨a, s, hs, rfl⟩ := hx
    have hs0 : (s : L) ≠ 0 := fun h => hs (by
      rw [show s = 0 from Subtype.ext h]; exact (RingHom.ker ψ).zero_mem)
    have hinv : (s : L)⁻¹ ∈ V := ⟨1, s, hs, by rw [map_one, one_mul]; rfl⟩
    have hsV : (s : L) ∈ V := hTA _ s.2
    have hu : IsUnit (⟨(s : L), hsV⟩ : S.ring) :=
      isUnit_iff_exists_inv.2 ⟨⟨(s : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
    have hord : S.ord (s : L) = 0 := S.ord_eq_zero (u := ⟨(s : L), hsV⟩) hu
    refine ⟨a, a.2, s, s.2, hs0, hord, ?_⟩
    change (a : L) * (s : L)⁻¹ * s = a
    rw [inv_mul_cancel_right₀ hs0]
  have hunit : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ψS : S.ring →+* K :=
    (IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (S := A) hunit).comp e.symm.toRingHom
  have hgen : ∀ (t : T) (h : (t : L) ∈ S.ring), ψS ⟨t, h⟩ = ψ t := by
    intro t h
    have h1 : e.symm ⟨t, h⟩ = algebraMap T A t := Subtype.ext rfl
    show IsLocalization.lift _ (e.symm ⟨t, h⟩) = ψ t
    rw [h1, IsLocalization.lift_eq]
  refine ⟨S, hS, ψS, fun z => ?_, fun a => ?_, fun t => hgen t _, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb0, e1⟩ := hR.frac z
    have hb : b ∈ (RingHom.ker ψ).primeCompl := fun h => hb0 (RingHom.mem_ker.1 h)
    refine ⟨e (IsLocalization.mk' A a ⟨b, hb⟩), ?_⟩
    show IsLocalization.lift _ (e.symm (e _)) = z
    rw [RingEquiv.symm_apply_apply, IsLocalization.lift_mk'_spec]
    exact e1.symm.trans (mul_comm _ _)
  · exact (hgen ⟨cL a, hT.const_mem a⟩ _).trans (hc a)
  · have h1 : (⟨f, hS.1 f f.2⟩ : S.ring) = e (algebraMap T A f) := Subtype.ext rfl
    rw [h1, MulEquiv.irreducible_iff]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax

end GlobalTheory.FieldPair.PrimeElementPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrPlace_of_prime_element_of_normal_localModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  first | exact @GlobalTheory.FieldPair.PrimeElementPlace.main | exact GlobalTheory.FieldPair.PrimeElementPlace.main | (intros; apply GlobalTheory.FieldPair.PrimeElementPlace.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.FieldPair.klt_of_klt_restrict : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  classical
  intro hP L K _ _ cL cK n T hT ψ f w θ hic hconst hker hf0 hRng hTr hsupp hEff hKlt
  obtain ⟨S, hS, ψS, hsurj, hcK, hcomp, hirr⟩ :=
    GlobalTheory.T.exists_dvrPlace_of_prime_element_of_normal_localModel cL cK n T hT ψ f hic hconst hker hf0 hRng

  let ι : T → S.ring := fun t => ⟨t, hS.1 t t.2⟩
  have hw : (fun i => ψS (ι (w i))) = fun i => ψ (w i) := funext fun i => hcomp (w i)
  have hTr' : TrBasis cK (fun i => ψS (ι (w i))) := by rw [hw]; exact hTr
  obtain ⟨hTrL, hform, hord, hord0⟩ :=
    GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts cL cK n S ψS (ι f) (fun i => ι (w i)) hsurj hcK hirr hTr'
  have hmapS : Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ) = Finsupp.mapDomain ψ θ := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext t
    exact hcomp t
  have hmapL : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.mapDomain ι θ) =
      Finsupp.mapDomain (fun g : T => (g : L)) θ := by
    rw [← Finsupp.mapDomain_comp]
    rfl
  have hsuppS : ∀ g ∈ (Finsupp.mapDomain ι θ).support, ψS g ≠ 0 := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    intro h
    exact hsupp t ht ((hcomp t).symm.trans h)
  have hrange : ∀ a ∈ ψ.range, ∃ t : T, ψS ⟨t, hS.1 t t.2⟩ = a := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, hcomp t⟩
  have hKlt' : Klt cK n ψ.range (dForm cK (fun i => ψS (ι (w i))))
      (Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ)) := by
    rw [hw, hmapS]
    exact hKlt
  have hadj := GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring cL cK n T S hS.1 ψS (ι f) (fun i => ι (w i))
    (Finsupp.mapDomain ι θ) ψ.range hsurj hcK hirr hTr' hsuppS hrange hKlt'
  have hadj' : AdjKlt cL (n + 1) T S
      (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ + Finsupp.single (f : L) 1) := by
    rw [← hmapL]
    exact hadj
  have hTrL' : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := hTrL
  have hform' : S.formOrd (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 :=
    hform
  have hord' : S.ord (f : L) = 1 := hord
  have hfL : (f : L) ≠ 0 := fun h => hf0 (Subtype.ext h)

  have hq : S.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun t ht => ?_
    have h0 : S.ord (t : L) = 0 :=
      hord0 (ι t) (fun h => hsupp t ht ((hcomp t).symm.trans h))
    simp [Function.comp, h0]
  have hdisc : S.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.disc, hform', hq]
    simp
  exact GlobalTheory.T.klt_of_adjunctionKlt_localModel hP cL (n + 1) T _ _ (f : L) S hT hic hTrL' f.2 hfL hS hord' hdisc hEff hadj'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrictStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.klt_of_klt_restrict_alt : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  first | exact @GlobalTheory.FieldPair.klt_of_klt_restrict | exact GlobalTheory.FieldPair.klt_of_klt_restrict | (intros; apply GlobalTheory.FieldPair.klt_of_klt_restrict <;> assumption)
end
