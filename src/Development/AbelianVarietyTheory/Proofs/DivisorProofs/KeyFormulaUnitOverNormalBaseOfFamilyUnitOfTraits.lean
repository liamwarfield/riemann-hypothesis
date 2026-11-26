module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueFieldMapAdicCompletionSurjective
open IsLocalRing

namespace GlobalTheory

theorem residueField_map_adicCompletion_surjective (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal W) 1 x)
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal W) 1)
  rw [map_sub, AlgHom.commutes, ← hw, Ideal.Quotient.algebraMap_eq, sub_self] at h1
  haveI : Nontrivial (W ⧸ maximalIdeal W ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal W).ne_top)
  exact not_isUnit_zero h1

theorem finite_residueField_of_dominating (D : Type*) [CommRing D] [IsDomain D] [IsLocalRing D]
    [IsNoetherianRing D] [Ring.DimensionLEOne D] (hD : ¬ IsField D) [Finite (ResidueField D)]
    (V : ValuationSubring (FractionRing D))
    (h1 : ∀ r, algebraMap D (FractionRing D) r ∈ V)
    [IsLocalHom ((algebraMap D (FractionRing D)).codRestrict V h1)] :
    Finite (ResidueField V) := by
  set f := (algebraMap D (FractionRing D)).codRestrict V h1 with hf
  letI : Algebra D V := f.toAlgebra
  haveI : IsLocalHom (algebraMap D V) := ‹IsLocalHom f›
  haveI : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  have hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b := by
    intro x
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    refine ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul] at hbc ⊢
    change algebraMap D (FractionRing D) c * x = algebraMap D (FractionRing D) b
    rw [mul_comm]; exact hbc
  have hm : maximalIdeal D ≠ ⊥ := fun h => hD (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  haveI := finite_quotient_span_of_birational hB ha0
  have hle : Ideal.span {algebraMap D V a} ≤ maximalIdeal V := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_nonunit (algebraMap D V) a ha
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ D hle).toLinearMap := by
    intro y
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ v, rfl⟩
  haveI : Module.Finite D (ResidueField V) := Module.Finite.of_surjective _ hsurj
  haveI : Module.Finite (ResidueField D) (ResidueField V) :=
    Module.Finite.of_restrictScalars_finite D _ _
  exact Module.finite_of_finite (ResidueField D)

theorem exists_complete_dvr_finite_residueField : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by
  intro D _ _ _ hN hdim hF
  have hD : ¬ IsField D := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim; exact zero_ne_one hdim
  haveI : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by simp [hdim])
  haveI : Ring.DimensionLEOne D :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating D (FractionRing D) (FractionRing D) hD
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hfin : Finite (ResidueField V) := finite_residueField_of_dominating D hD V h1
  obtain ⟨hi, hl⟩ := injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap D (FractionRing D)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, hi, hl,
    Finite.of_surjective _ (residueField_map_adicCompletion_surjective V)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoiding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOne
namespace GlobalTheory

theorem exists_prime_notMem_ringKrullDim_quotient_eq_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R),
      h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R →
      ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  intro R _ _ _ _ h h0 hhm
  obtain ⟨q, hq, -, h1⟩ := exists_mem_height_map_le_one (IsLocalRing.maximalIdeal R)
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hqm : q.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hmax : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have : IsLocalRing (R ⧸ q.asIdeal) := IsLocalRing.of_surjective' _ hsurj
  have he : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal) =
      IsLocalRing.maximalIdeal (R ⧸ q.asIdeal) := IsLocalRing.eq_maximalIdeal hmax
  rw [he] at h3
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h3]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R), h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R → ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  first | exact @GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one | exact GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one | (intros; apply GlobalTheory.exists_prime_notMem_ringKrullDim_quotient_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoiding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem isJacobsonRing_int_of_dim_one : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_trait_finite_residueField_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  intro B _ _ _ _ m h hm hh
  classical

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int_of_dim_one
  haveI : Algebra.FiniteType ℤ (B ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m)
  set p := ringChar (B ⧸ m) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (B ⧸ m) 0 := h0 ▸ ringChar.charP (B ⧸ m)
    haveI : CharZero (B ⧸ m) := CharP.charP_to_charZero _
    haveI : Algebra.IsIntegral ℤ (B ⧸ m) := Algebra.IsIntegral.of_finite ℤ _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (algebraMap ℤ (B ⧸ m)).injective_int (Field.toIsField _))
  haveI : CharP (B ⧸ m) p := ringChar.charP (B ⧸ m)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) p).resolve_right hp0⟩
  letI : Algebra (ZMod p) (B ⧸ m) := ZMod.algebra (B ⧸ m) p
  haveI : IsScalarTower ℤ (ZMod p) (B ⧸ m) := AddCommGroup.intIsScalarTower
  haveI : Algebra.FiniteType (ZMod p) (B ⧸ m) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (B ⧸ m)
  haveI : Module.Finite (ZMod p) (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing (ZMod p) (B ⧸ m)
  haveI hfin : Finite (B ⧸ m) := Module.finite_of_finite (ZMod p)
  have hpm : (p : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let R := Localization.AtPrime m
  haveI hRn : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors m)
  have hx0 : algebraMap B R (h * p) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B R)]; exact fun e => mul_ne_zero hh hpB (hinj e)
  have hxm : algebraMap B R (h * p) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R m _).mpr (m.mul_mem_left h hpm)
  obtain ⟨q, hq, hnq, hdim⟩ := GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one R (algebraMap B R (h * p)) hx0 hxm
  let D := R ⧸ q
  haveI : IsDomain D := Ideal.Quotient.isDomain q
  haveI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let φ : B →+* D := (Ideal.Quotient.mk q).comp (algebraMap B R)
  have hcompR : Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hcomp : Ideal.comap φ (IsLocalRing.maximalIdeal D) = m := by
    rw [← Ideal.comap_comap, hcompR]; exact Localization.AtPrime.under_maximalIdeal
  have hφh : φ h ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_right _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  have hφp : φ (p : B) ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_left _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  haveI hD0 : CharZero D := by
    haveI : CharP D (ringChar D) := ringChar.charP D
    rcases CharP.char_is_prime_or_zero D (ringChar D) with hl | hl
    · exfalso
      have hlm' : ((ringChar D : ℕ) : B) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal D) := by
        rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]; exact zero_mem _
      have hlm : ((ringChar D : ℕ) : B) ∈ m := hcomp.le hlm'
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hlm
      have hdvd : p ∣ ringChar D := (CharP.cast_eq_zero_iff (B ⧸ m) p _).mp hlm
      have hpl : p = ringChar D :=
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).mp hdvd)
      apply hφp; rw [map_natCast, hpl, CharP.cast_eq_zero]
    · haveI : CharP D 0 := hl ▸ ringChar.charP D
      exact CharP.charP_to_charZero D

  have hsurj : Function.Surjective ((IsLocalRing.residue D).comp φ) := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hsR := IsLocalization.surjective_quotientMap_of_maximal_of_localization m.primeCompl R
      (I := IsLocalRing.maximalIdeal R) (J := m)
      (H := le_of_eq Localization.AtPrime.under_maximalIdeal.symm)
      (by rw [Localization.AtPrime.under_maximalIdeal]; exact hm)
    obtain ⟨bb, hb⟩ := hsR (Ideal.Quotient.mk _ r)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bb
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hb
    simp only [RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hb' : algebraMap B R b - r ∈ Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) :=
      hcompR ▸ hb
    simpa [φ, map_sub] using hb'
  have hker : ∀ b ∈ m, ((IsLocalRing.residue D).comp φ) b = 0 := by
    intro b hb
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hcomp]; exact hb
  haveI hresfin : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_surjective (Ideal.Quotient.lift m _ hker) (by
      intro y; obtain ⟨b, rfl⟩ := hsurj y; exact ⟨Ideal.Quotient.mk m b, rfl⟩)
  obtain ⟨V, _, _, _, hcV, g, hg, hgl, hVfin⟩ :=
    GlobalTheory.exists_complete_dvr_finite_residueField D inferInstance hdim hresfin
  haveI : CharZero V := ⟨fun a b e => by
    apply Nat.cast_injective (R := D); apply hg; rw [map_natCast, map_natCast]; exact e⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, g.comp φ, hcV, hVfin, ?_, ?_⟩
  · rw [RingHom.comp_apply]; intro e; apply hφh; apply hg; rw [e, map_zero]
  · have hgm : Ideal.comap g (IsLocalRing.maximalIdeal V) = IsLocalRing.maximalIdeal D := by
      ext x; simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    rw [← Ideal.comap_comap, hgm, hcomp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoidingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  first | exact @GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | exact GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | (intros; apply GlobalTheory.exists_trait_finite_residueField_charZero_avoiding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem dvd_of_forall_fintrait : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  intro A _ _ _ _ _ a f hf H
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero f
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hfK : algebraMap A K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  let y : K := algebraMap A K f / algebraMap A K a
  have hy : y ≠ 0 := div_ne_zero hfK haK
  let S := Algebra.adjoin A {y}
  let z : S := ⟨y, Algebra.self_mem_adjoin_singleton A y⟩
  by_cases hz : IsUnit z
  · obtain ⟨w, hw⟩ := hz.exists_right_inv
    have hw' : (w : K) = y⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy (hw' ▸ w.2))
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, inv_div, mul_div_cancel₀ _ hfK]
  · exfalso
    have hft : Algebra.FiniteType A S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
    haveI hftZ : @Algebra.FiniteType ℤ S _ _ (Ring.toIntAlgebra S) := by
      have h2 := Algebra.FiniteType.trans (R := ℤ) (S := A) (A := S) inferInstance hft
      convert h2 using 1 <;> first | rfl | exact Subsingleton.elim _ _
    have hinjS : Function.Injective (algebraMap A S) := fun b c h => hinj (congrArg Subtype.val h)
    have : CharZero S := charZero_of_injective_algebraMap hinjS
    obtain ⟨n, hn, hzn⟩ := exists_max_ideal_of_mem_nonunits hz
    have hfS : algebraMap A S f ≠ 0 := (map_ne_zero_iff _ hinjS).2 hf
    obtain ⟨V, _, _, _, _, t, hc, hfin, htf, hcomap⟩ := GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding S n (algebraMap A S f) hn hfS
    have hdiv := H V hc hfin (t.comp (algebraMap A S)) htf
    simp only [RingHom.comp_apply] at hdiv
    have hfa : algebraMap A S f = z * algebraMap A S a := by
      apply Subtype.ext
      show algebraMap A K f = (algebraMap A K f / algebraMap A K a) * algebraMap A K a
      rw [div_mul_cancel₀ _ haK]
    have htz : t z ∈ IsLocalRing.maximalIdeal V := by
      rw [← Ideal.mem_comap, hcomap]; exact hzn
    rw [hfa, map_mul] at hdiv htf
    obtain ⟨c, hc'⟩ := hdiv
    have hta : t (algebraMap A S a) ≠ 0 := right_ne_zero_of_mul htf
    have h1 : t z * c = 1 := by
      apply mul_left_cancel₀ hta
      calc t (algebraMap A S a) * (t z * c) = t z * t (algebraMap A S a) * c := by ring
        _ = t (algebraMap A S a) := hc'.symm
        _ = t (algebraMap A S a) * 1 := (_root_.mul_one _).symm
    exact (IsLocalRing.mem_maximalIdeal _).1 htz ⟨⟨t z, c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.KeyEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  first | exact @GlobalTheory.KeyEven.dvd_of_forall_fintrait | exact GlobalTheory.KeyEven.dvd_of_forall_fintrait | (intros; apply GlobalTheory.KeyEven.dvd_of_forall_fintrait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisPullbackGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KeyExtLie

theorem dnRingHom_ext {R S : Type} [CommRing R] [CommRing S] {f f' : DualNumber R →+* S}
    (h1 : ∀ a, f (TrivSqZeroExt.inl a) = f' (TrivSqZeroExt.inl a)) (h2 : f DualNumber.eps = f' DualNumber.eps) : f = f' := by
  refine RingHom.ext fun x => ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * DualNumber.eps := by
    ext <;> simp
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyExtLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEvenBC

theorem keyOn_pullback : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  intro A B K _ _ _ f h G _ _ L σ x y hG hy hσ hK _
  obtain ⟨φ, he, ψ, F, hφ, hψ, hrig, hsec, hF1, hF2, hFv⟩ := hK
  have hP := isGrpPullback_pullback G (spMap f)
  have sqφ : φ ≫ G.hom = (x.P.A.hom ≫ spMap h) ≫ spMap f := by
    rw [Category.assoc, ← spMap_comp]
    exact hφ.1.w
  obtain ⟨φ', hφ', hfst, hsnd⟩ : ∃ φ' : x.P.A.left ⟶ ((Over.pullback (spMap f)).obj G).left,
      IsGrpPullback x.P.A ((Over.pullback (spMap f)).obj G) (spMap h) φ' ∧ φ' ≫ pullback.fst G.hom (spMap f) = φ ∧
        φ' ≫ ((Over.pullback (spMap f)).obj G).hom = x.P.A.hom ≫ spMap h := by
    refine ⟨pullback.lift φ (x.P.A.hom ≫ spMap h) sqφ, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, ← spMap_comp]
    exact hφ
  subst hfst
  have hL := L.isLB
  have hL' : (L.L.pull (pullback.fst G.hom (spMap f))).IsLB := LB.isLB_pull hL _
  have heF : eSec ((Over.pullback (spMap f)).obj G) ≫ pullback.fst G.hom (spMap f) = spMap f ≫ eSec G :=
    PolBaseChange.eSec_comm hP
  let L' : RigLB ((Over.pullback (spMap f)).obj G) :=
    ⟨L.L.pull (pullback.fst G.hom (spMap f)), rigPullOf (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L L.rig, hL',
      Out.LBxP.isGen_pullAlong L.L (pullback.fst G.hom (spMap f)) (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1)
        (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => heF) L.rig L.rigGen⟩
  have he' : eSec x.P.A ≫ φ' = spMap h ≫ eSec ((Over.pullback (spMap f)).obj G) := PolBaseChange.eSec_comm hφ'
  have pw := (isGen_iff (L := L.L) (F := pullback.fst G.hom (spMap f)) (idIso _)).1 (idIso_isGen hL')
  obtain ⟨σ', hσ'⟩ := sec_pull_down pw hL hL' σ
  have pψ := (isGen_iff ψ).1 hψ
  obtain ⟨w', T⟩ := exists_cancel hL (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) ψ pw pψ hL' x.P.isLB
  have H : PMaps (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) (K := PUnit)
      (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (spMap f) :=
    (maps_iff _ _ _ _ L'.rig L.rig (spMap f) L'.rig (rigPull_le (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L) (fun _ => rfl)).1 (idIso_maps L')
  have H'' : PMaps ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec G) (fun _ => 1) x.rig L.rig
      (spMap h ≫ spMap f) := by
    rw [← spMap_comp]
    exact (maps_iff ψ _ _ _ x.rig L.rig (spMap (h.comp f)) _ (rigPull_le (G' := x.P.A) (φ' ≫ pullback.fst G.hom (spMap f)) (spMap (h.comp f)) he L.L)
      (fun _ => rfl)).1 hrig
  have H' := T.pmaps_cancel hL (fun _ => he') H H''
  have hrig' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ' (spMap h) he' L'.L L'.rig) :=
    (maps_iff w' _ _ _ x.rig L'.rig (spMap h) _ (rigPull_le φ' (spMap h) he' L'.L) (fun _ => rfl)).2 H'

  have hsec' : ∀ (j : (L'.L.pull φ').ι) (i : x.P.L.ι) (hh : (L'.L.pull φ').U j ⊓ x.P.L.U i ≤ φ' ⁻¹ᵁ L'.L.U (j PUnit.unit)),
      (φ'.appLE _ _ hh).hom (σ'.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L'.L.pull φ').U j ⊓ x.P.L.U i) from (w'.s (j, i)).val) * resG _ inf_le_right (x.th.f i) := by
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk w' σ' x.th ?_
    intro z J k hJ hk
    have ha : (pullback.fst G.hom (spMap f)) (φ' z) ∈ L.L.U (J PUnit.unit) := mem_pull.1 hJ
    have hW : (𝟙 x.P.A.left) z ∈ (L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k :=
      ⟨mem_pull.2 ha, hk⟩
    have s2 : gs (𝟙 _ ≫ φ' ≫ pullback.fst G.hom (spMap f)) z _ (σ.f (J PUnit.unit)) =
        (gw ψ (𝟙 _) z (J PUnit.unit) k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e := congrArg (gs (𝟙 _) z ((L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k))
        (hsec (fun _ => J PUnit.unit) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE (φ' ≫ pullback.fst G.hom (spMap f)) _ _ _ (𝟙 _) z hW _).symm.trans (e.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := hσ' _ (𝟙 _ ≫ φ') z (J PUnit.unit) J ha hJ
    have e3 := T _ (𝟙 _) z (J PUnit.unit) J k ha hJ hk
    rw [Category.assoc] at e1
    rw [e1, e3, Units.val_mul, _root_.mul_assoc] at s2
    exact (Units.mul_right_inj _).1 s2
  have hnz : NzFib (L := L'.L) σ' := by
    intro s
    obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y0, rfl, hy0⟩ := Scheme.exists_preimage_of_isPullback hP.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y0, hy0, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs (pullback.fst G.hom (spMap f)) y0 _ (σ.f k)) := by
      rw [gs_stalkMap _ y0 _ hk]; exact u.map _
    have e := hσ' _ (𝟙 _) y0 k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)

  have := hG.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y i).left) ≫ G.hom = (epsR B).hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let y' : Fin x.P.g → (epsR B ⟶ ((Over.pullback (spMap f)).obj G)) := fun i =>
    Over.homMk (hP.1.lift _ _ (sq i)) (hP.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap f) = spMap (Chart.dualMapR f) ≫ (y i).left :=
    fun i => hP.1.lift_fst _ _ _
  have hadd : ∀ (a b : B) (w : Chart.sp (DualNumber B) ⟶ ((Over.pullback (spMap f)).obj G)), Chart.IsTan w →
      Chart.spMap (Chart.scaleD (a + b)) ≫ w = (Chart.spMap (Chart.scaleD a) ≫ w) * (Chart.spMap (Chart.scaleD b) ≫ w) :=
    fun a b w hw => GlobalTheory.LieMultiple.scale_add ((Chart.isTan_iff w).1 hw) a b
  have hT : ∀ i, IsTangent (y' i) := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hy', show η[((Over.pullback (spMap f)).obj G)].left = eSec ((Over.pullback (spMap f)).obj G) from rfl, heF, ← Category.assoc]
      have e0 := hy.1 i
      rw [IsTangent] at e0
      rw [show eSec G = η[G].left from rfl, ← e0, ← Category.assoc]
      congr 1
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      simp [Chart.dualMapR]
    · rw [Category.assoc, Over.w (y' i), Over.w η[((Over.pullback (spMap f)).obj G)]]
      show Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      convert Spec.map_id (CommRingCat.of B)
      ext a; simp
  have hLie : IsLieBasis y' := Chart.frameLieBCR G hy f hP hadd hT hy'

  have hF' : F = (Chart.dualMapR h).comp (Chart.dualMapR f) := by
    refine GlobalTheory.KeyExtLie.dnRingHom_ext (fun a => ?_) ?_
    · have e1 := hF1 a
      simp only [TrivSqZeroExt.algebraMap_eq_inl] at e1
      rw [e1]
      simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [hF2]
      ext <;> simp [Chart.dualMapR]
  have hv' : ∀ i, (x.v i).left ≫ φ' = spMap (Chart.dualMapR h) ≫ (y' i).left := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hFv i, Category.assoc, hy', ← Category.assoc, hF', spMap_comp]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x.v i), Category.assoc, Over.w (y' i)]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨L', σ', y', ⟨idIso _, idIso_isGen hL'⟩, hLie, hnz, φ', he', w', Chart.dualMapR h, hφ',
    (isGen_iff w').2 (T.pgen_cancel hL pw pψ), hrig', hsec', fun a => ?_, ?_, hv'⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyEvenBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  first | exact @GlobalTheory.KeyEvenBC.keyOn_pullback | exact GlobalTheory.KeyEvenBC.keyOn_pullback | (intros; apply GlobalTheory.KeyEvenBC.keyOn_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven.LocPf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (h : m = n)
    (y : Fin n → (epsR R ⟶ G)) (hy : IsLieBasis y) : IsLieBasis (fun i : Fin m => y (i.cast h)) := by
  subst h
  exact hy

theorem exists_away_subset {A : Type} [CommRing A] [IsDomain A] (U : Set (Sp A)) (hU : IsOpen U)
    (hgen : Set.range (spMap (algebraMap A (FractionRing A))) ⊆ U) :
    ∃ f : A, f ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away f))) ⊆ U := by
  obtain ⟨q⟩ : Nonempty (Sp (FractionRing A)) := inferInstance
  have hp := hgen ⟨q, rfl⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := (spMap (algebraMap A (FractionRing A)) q : PrimeSpectrum A)) hp hU
  refine ⟨r, ?_, ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpr (Ideal.zero_mem _)
  · rw [show Set.range (spMap (algebraMap A (Localization.Away r))) =
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hrU

theorem mem_range_of_traits {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [Algebra.FiniteType ℤ A] (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : V, h b = algebraMap V (FractionRing V) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue A a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ _ hc hfin t ht
    by_cases htf0 : t f = 0
    · cases n with
      | zero => simp
      | succ k => exact absurd (by rw [map_pow, htf0, zero_pow (Nat.succ_ne_zero k)]) ht
    have htf : t f ≠ 0 := htf0
    have hinjV := IsFractionRing.injective V (FractionRing V)
    have hu : IsUnit (((algebraMap V (FractionRing V)).comp t) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := H V hc hfin t htf _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    rw [← e', ← hn, map_pow, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

end GlobalTheory.KeyEven.LocPf

namespace GlobalTheory.KeyEven.LocPf

theorem keyLoc_of_famUnit_keyTrait : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  intro κ hFU hKT A _ _ _ _ _ G _ _ L σ x y hG hsm hopen hsym hpol hunif hy hσ hkey
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper hG hpb.1
  obtain ⟨f, hf0, hfab⟩ := exists_away_subset (abLocus G) hopen hab
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) G L σ x.P.g y x.g_pos hG hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hFU (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : Vˣ, h u = algebraMap V (FractionRing V) w := by
    intro V _ _ _ _ hcomp hfin t ht h hh
    have hrange : Set.range (spMap ((algebraMap V (FractionRing V)).comp t)) ⊆ abLocus G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing V) ((algebraMap V _).comp t) G L σ x.P.g y x.g_pos hG hsm
      hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing V) (algebraMap A _) h G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    obtain ⟨L', σ', y', hiso, hy', hσ', hk'⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing V) t (algebraMap V _) G L σ xV
      (fun i => y (i.cast hgV)) hG (isLieBasis_cast hgV y hy) hσ hkV
    have hne : (spMap t ⁻¹' abLocus G).Nonempty := by
      obtain ⟨q⟩ : Nonempty (Sp (FractionRing V)) := inferInstance
      exact ⟨spMap (algebraMap V _) q, hrange ⟨q, rfl⟩⟩
    obtain ⟨D, A', U, hU⟩ := hunif V hcomp hfin (spMap t) hne
    obtain ⟨w, hw⟩ := hKT V hcomp hfin _ L' σ' xV y' (IsSemiAbelian.pullback _ G hG)
      ⟨D, A', U, LBIso.trans U.LG.isLB (pull_isLB L.isLB _) L'.isLB hU hiso⟩ hy' hσ' hk'
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_traits f hf0 (u : Localization.Away f) (fun V _ _ _ _ hcomp hfin t ht h hh => by
    obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_traits f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ _ hcomp hfin t ht h hh => by
      obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
      refine ⟨((w⁻¹ : Vˣ) : V), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end GlobalTheory.KeyEven.LocPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  first | exact @GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | exact GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | (intros; apply GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait <;> assumption)
end
