module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRField

theorem eq_pow_mul_unit {R : Type} [CommRing R] (π : R) (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (y : R) (hy : y ≠ 0) : ∃ (n : ℕ) (u : R), IsUnit u ∧ y = π ^ n * u := by
  classical
  have h : ∃ n : ℕ, ¬ π ^ n ∣ y := by
    by_contra h
    push Not at h
    exact hy (hsep y h)
  have h0 : Nat.find h ≠ 0 := by
    intro e
    have := Nat.find_spec h
    rw [e] at this
    exact this (by simp)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 : π ^ n ∣ y := by
    by_contra hc
    have := Nat.find_min' h hc
    omega
  obtain ⟨u, rfl⟩ := h1
  refine ⟨n, u, hu u ?_, rfl⟩
  intro hd
  have := Nat.find_spec h
  rw [hn] at this
  exact this (by rw [pow_succ]; exact mul_dvd_mul_left _ hd)

theorem general {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial R] (M : Submonoid R)
    [IsLocalization M S] (π : R) (hreg : ∀ y : R, π * y = 0 → y = 0)
    (hsep : ∀ y : R, (∀ n : ℕ, π ^ n ∣ y) → y = 0)
    (hu : ∀ y : R, ¬ π ∣ y → IsUnit y) (hπ : π ∈ M) (hM : ∀ m ∈ M, ∃ n : ℕ, m ∣ π ^ n) :
    IsDomain R ∧ Function.Injective (algebraMap R S) ∧ IsField S ∧
      ∀ x : S, ∃ (n : ℕ) (y : R), x * algebraMap R S π ^ n = algebraMap R S y := by
  have hregn : ∀ (n : ℕ) (y : R), π ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y h; simpa using h
    | succ n ih => intro y h; exact ih y (hreg _ (by rw [← h]; ring))
  have : NoZeroDivisors R := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu a ha
    right
    rw [mul_assoc] at h
    exact (hu'.mul_right_eq_zero).1 (hregn n _ h)⟩
  have hD : IsDomain R := NoZeroDivisors.to_isDomain R
  have hle : M ≤ nonZeroDivisors R := by
    intro m hm
    obtain ⟨n, c, hc⟩ := hM m hm
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have := hregn n 1 (by rw [hc]; ring)
    exact one_ne_zero this
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hle
  have : Nontrivial S := hinj.nontrivial
  refine ⟨hD, hinj, ⟨exists_pair_ne S, mul_comm, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M a
    have hm : IsUnit (algebraMap R S m) := IsLocalization.map_units S m
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hy
      exact ha (hm.mul_left_eq_zero.1 hy)
    obtain ⟨n, u, hu', rfl⟩ := eq_pow_mul_unit π hsep hu y hy0
    have hyu : IsUnit (algebraMap R S (π ^ n * u)) := by
      rw [map_mul, map_pow]
      exact ((IsLocalization.map_units S (⟨π, hπ⟩ : M)).pow n).mul (hu'.map _)
    simp only at hy
    rw [← hy] at hyu
    exact (isUnit_of_mul_isUnit_left hyu).exists_right_inv
  · intro x
    obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj M x
    obtain ⟨n, c, hc⟩ := hM m m.2
    refine ⟨n, y * c, ?_⟩
    simp only at hy
    rw [← map_pow, hc, map_mul, map_mul, ← mul_assoc, hy]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro e
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val e

theorem of_isEps (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧
      ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨hF, hreg, hc, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  haveI : IsLocalization.Away (aDp l (xi e)) (Per.BdR l) := GlobalTheory.CrisLoc.bdR_away l _ hk
  refine general (Submonoid.powers (aDp l (xi e))) (aDp l (xi e)) hreg ?_ ?_ ?_ ?_
  · intro y hy
    refine hc.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hy n
  · intro y hy
    refine hu y fun h => hy ?_
    have := (hF 1 y).1 ((hθ y).1 h)
    rwa [pow_one] at this
  · exact Submonoid.mem_powers _
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, dvd_rfl⟩

theorem bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2, h3, -⟩ := of_isEps l e he
  exact ⟨h1, h2, h3, fun e' he' => (of_isEps l e' he').2.2.2⟩

end GlobalTheory.MemLoc.BdRField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_isDomain_bdR_isField : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.BdRp l) ∧ Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ IsField (Per.BdR l) ∧ ∀ e : Per.Fl l, IsEps e → ∀ x : Per.BdR l, ∃ (n : ℕ) (y : Per.BdRp l), x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @GlobalTheory.MemLoc.BdRField.bdR_isField | exact GlobalTheory.MemLoc.BdRField.bdR_isField | (intros; apply GlobalTheory.MemLoc.BdRField.bdR_isField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing

namespace GlobalTheory

theorem finite_integralClosure_of_isLocalization {R S L : Type*} [CommRing R] [CommRing S]
    [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R L)
  let f : integralClosure R L → integralClosure S L := fun z => ⟨z, IsIntegral.tower_top z.2⟩
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (Rₘ := S) (y : L) y.2
  have key : ∀ z ∈ Submodule.span R (s : Set (integralClosure R L)),
      f z ∈ Submodule.span S (↑(s.image f) : Set (integralClosure S L)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
    | zero =>
      have : f 0 = 0 := rfl
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := rfl
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : f (a • x) = algebraMap R S a • f x := by
        apply Subtype.ext
        change a • (x : L) = algebraMap R S a • (x : L)
        rw [algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hz : (⟨m • (y : L), hm⟩ : integralClosure R L) ∈ Submodule.span R (s : Set _) :=
    hs ▸ Submodule.mem_top
  have e : y = IsLocalization.mk' S (1 : R) m • f ⟨m • (y : L), hm⟩ := by
    apply Subtype.ext
    change (y : L) = IsLocalization.mk' S (1 : R) m • ((m : R) • (y : L))
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L, ← mul_assoc,
      ← map_mul, IsLocalization.mk'_spec, map_one, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ hz)

theorem finite_integralClosure_of_essFiniteType_int :
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      Module.Finite D (integralClosure D (FractionRing D)) := by
  intro D _ _ _
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ D).mp inferInstance
  let K := FractionRing D
  have hinj : Function.Injective (algebraMap S₀ D) := Subtype.val_injective
  haveI hfr : IsFractionRing S₀ K := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors D) K
      (fun x hx => hx.mem_nonZeroDivisors)
    have e : (nonZeroDivisors D).comap (algebraMap S₀ D) = nonZeroDivisors S₀ := by
      ext x
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
      exact (map_eq_zero_iff _ hinj).not
    rw [e] at h
    exact h
  suffices h : Module.Finite S₀ (integralClosure S₀ K) from
    finite_integralClosure_of_isLocalization M
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | h0
  · haveI : Fact (ringChar D).Prime := ⟨hp⟩
    haveI : CharP D (ringChar D) := ringChar.charP D
    haveI : CharP S₀ (ringChar D) := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff D]⟩
    letI : Algebra (ZMod (ringChar D)) S₀ := (ZMod.castHom dvd_rfl S₀).toAlgebra
    haveI : Algebra.FiniteType (ZMod (ringChar D)) S₀ :=
      .of_restrictScalars_finiteType ℤ (ZMod (ringChar D)) S₀
    exact NormFin.finite_integralClosure_of_perfectField (ZMod (ringChar D)) S₀ K K
  · haveI : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp h0
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
    haveI : Algebra.EssFiniteType S₀ D := .of_isLocalization D M
    haveI : Algebra.EssFiniteType D K := .of_isLocalization K (nonZeroDivisors D)
    haveI : Algebra.EssFiniteType S₀ K := .comp S₀ D K
    exact GlobalTheory.finite_integralClosure_of_essFiniteType_field ℤ S₀ K

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem mem_FilD_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  intro l _ e he a x
  have h := (GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he).1
  have hg : ∀ (n : ℕ) (x : Per.BdR l), x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    GlobalTheory.CrisLoc.mem_fil_neg l _ (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he)
  generalize aDp l (xi e) = ξ at h hg ⊢
  have hn : ∀ (n : ℕ) (w : Per.BdR l), w ∈ Per.FilD l (n : ℤ) ↔
      ∃ y : Per.BdRp l, w = algebraMap (Per.BdRp l) (Per.BdR l) (ξ ^ n * y) := by
    intro n w
    constructor
    · intro hw
      obtain ⟨z, hz, ez⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l hw
      obtain ⟨y, rfl⟩ := (h _ _).1 hz
      exact ⟨y, ez.symm⟩
    · rintro ⟨y, rfl⟩
      exact GlobalTheory.RingIface.alg_mem_FilD_nat l ((h _ _).2 (dvd_mul_right _ _))
  rcases le_total 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hn, Int.toNat_neg_natCast, Int.toNat_natCast, pow_zero, mul_one]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha
    rw [hg, neg_neg, Int.toNat_neg_natCast, Int.toNat_natCast]
    simp only [pow_zero, one_mul]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  first | exact @GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | exact GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | (intros; apply GlobalTheory.MemLoc.mem_FilD_iff_xi_pow <;> assumption)
end
end
