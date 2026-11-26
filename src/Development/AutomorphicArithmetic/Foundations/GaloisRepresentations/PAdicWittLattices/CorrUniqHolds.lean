module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvariStatement
public import Development.EtaleCohomology.KummerExtensions.EtaleTateTwistSectionsLocallyGenerated
public import Development.EtaleCohomology.KummerExtensions.EtaleRootsOfUnityReductionGenerator
public import Development.EtaleCohomology.WeilConjectures.AdicFinPf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleDuality.FinAdicFin
namespace LateralTheory.Fin.AdicFin
theorem etale_torsion_cohomology_residue_basic : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties := by
  apply LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_properties_of_mathlib
theorem etale_bockstein_derived_category_dictionary : LateralTheory.KummerTheory.BockCut.DerDict := by
  apply LateralTheory.KummerTheory.DerDictPf.DerDict_of <;> first | exact etale_torsion_cohomology_residue_basic
theorem etale_bockstein_long_exact_sequence_natural : LateralTheory.KummerTheory.BockCut.NatLES := by
  apply LateralTheory.KummerTheory.NatLESPf.NatLES_of <;> first | exact etale_bockstein_derived_category_dictionary
theorem etale_bockstein_integer_hom_compat : LateralTheory.KummerTheory.BockCut.ZHom := by
  apply LateralTheory.KummerTheory.ZHomPf.ZHom_of
theorem etale_torsion_cohomology_twist_section : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated := by
  apply LateralTheory.Ext.etale_tate_twist_sections_locally_generated
theorem etale_torsion_cohomology_primary_part_basic : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  apply LateralTheory.EtaleFoundations.PrimPf.cyclotomic_primitive_root_product_identities_of_adjoin_root
theorem etale_bockstein_reduction_exact : LateralTheory.KummerTheory.BockCut.RedEx := by
  apply LateralTheory.KummerTheory.RedExPf.RedEx_of <;> first | exact etale_bockstein_integer_hom_compat | exact etale_torsion_cohomology_twist_section | exact etale_torsion_cohomology_primary_part_basic
theorem etale_torsion_cohomology_mono_epi_of_exact : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_mono_epi_iff_sections_of_separation
theorem etale_bockstein_twisted_extension : LateralTheory.KummerTheory.BockCut.TwExt := by
  apply LateralTheory.KummerTheory.TwExtPf.TwExt_of <;> first | exact etale_torsion_cohomology_twist_section | exact etale_torsion_cohomology_mono_epi_of_exact
theorem etale_locally_exists_primitive_root_of_unity : LateralTheory.EtaleFoundations.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  apply LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order
theorem etale_torsion_cohomology_primary_localization_kummer : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  apply LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order
theorem etale_torsion_cohomology_primary_localization : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := by
  apply LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer <;> first | exact etale_locally_exists_primitive_root_of_unity | exact etale_torsion_cohomology_primary_localization_kummer
theorem etale_torsion_cohomology_localization_basic : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := by
  apply LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties
theorem etale_bockstein_reduction_surjective : LateralTheory.KummerTheory.BockCut.RedEpi := by
  apply LateralTheory.KummerTheory.RedEpiPf.RedEpi_of <;> first | exact etale_torsion_cohomology_twist_section | exact etale_torsion_cohomology_primary_part_basic | exact etale_torsion_cohomology_primary_localization | exact etale_torsion_cohomology_mono_epi_of_exact | exact etale_torsion_cohomology_localization_basic
theorem etale_bockstein_reduction_kernel_eq_image : LateralTheory.KummerTheory.BockCut.RedKer := by
  apply LateralTheory.KummerTheory.RedKerPf.RedKer_of <;> first | exact etale_torsion_cohomology_twist_section | exact etale_torsion_cohomology_primary_part_basic | exact etale_torsion_cohomology_localization_basic | exact etale_torsion_cohomology_mono_epi_of_exact
theorem etale_sheaf_short_complex_exact_iff_locally_lifts : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds
theorem etale_bockstein_twisted_short_exact_sequence : LateralTheory.KummerTheory.BockCut.TwSES := by
  apply LateralTheory.KummerTheory.TwSESPf.TwSES_of <;> first | exact etale_bockstein_reduction_surjective | exact etale_bockstein_reduction_kernel_eq_image | exact etale_torsion_cohomology_mono_epi_of_exact | exact etale_sheaf_short_complex_exact_iff_locally_lifts | exact etale_torsion_cohomology_localization_basic
theorem etale_bockstein_restriction_of_resolution : LateralTheory.KummerTheory.BockCut.RestrRes := by
  apply LateralTheory.KummerTheory.RestrResPf.RestrRes_of <;> first | exact etale_sheaf_short_complex_exact_iff_locally_lifts | exact etale_torsion_cohomology_residue_basic
theorem etale_torsion_cohomology_operation_comp : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible := by
  apply LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange
theorem etale_torsion_cohomology_extension_hom_left_compat : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds
theorem etale_torsion_cohomology_extension_hom_right_compat : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  apply LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds
theorem etale_torsion_cohomology_extension_hom_exists : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity <;> first | exact etale_torsion_cohomology_extension_hom_left_compat | exact etale_torsion_cohomology_extension_hom_right_compat
theorem etale_bockstein_connecting_map_unique_up_to_sign : LateralTheory.KummerTheory.BockCut.SemiUniq := by
  apply LateralTheory.KummerTheory.SemiUniqPf.SemiUniq_of <;> first | exact etale_bockstein_restriction_of_resolution | exact etale_bockstein_integer_hom_compat | exact etale_torsion_cohomology_operation_comp | exact etale_torsion_cohomology_extension_hom_exists | exact etale_torsion_cohomology_residue_basic | exact etale_torsion_cohomology_mono_epi_of_exact
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
theorem etale_prime_power_twist_reduction_map_exists : LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator := by
  apply LateralTheory.Ext.etale_roots_of_unity_reduction_generator
theorem etale_torsion_cohomology_restriction_hom_exact : LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsFunctorExact := by
  apply LateralTheory.EtaleFoundations.etaleSheaf_restrictScalars_functor_exact_of_adjoints
theorem etale_torsion_cohomology_restriction_hom_exists : LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  apply LateralTheory.EtaleFoundations.etaleSheaf_restrictScalars_resolution_hom_exists_of_exact <;> first | exact etale_torsion_cohomology_restriction_hom_exact
theorem etale_prime_power_twist_restriction_exists : LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible := by
  apply LateralTheory.EtaleFoundations.etaleSheaf_restrictScalars_resolution_comparison_of_hom <;> first | exact etale_torsion_cohomology_restriction_hom_exists
theorem etale_bockstein_reduction_postcomposition_compat : LateralTheory.KummerTheory.BockCut.RedPost := by
  apply LateralTheory.KummerTheory.RedPostPf.RedPost_of <;> first | exact etale_bockstein_connecting_map_unique_up_to_sign | exact etale_bockstein_twisted_extension | exact etale_bockstein_integer_hom_compat | exact etale_torsion_cohomology_operation_spec | exact etale_torsion_cohomology_operation_comp | exact etale_prime_power_twist_reduction_map_exists | exact etale_prime_power_twist_restriction_exists | exact etale_torsion_cohomology_primary_part_basic | exact etale_torsion_cohomology_residue_basic
theorem etale_bockstein_sequence_adic_finiteness : LateralTheory.KummerTheory.Bock := by
  apply LateralTheory.KummerTheory.BockCut.goal_of <;> first | exact etale_bockstein_derived_category_dictionary | exact etale_bockstein_long_exact_sequence_natural | exact etale_bockstein_integer_hom_compat | exact etale_bockstein_reduction_exact | exact etale_bockstein_twisted_extension | exact etale_bockstein_reduction_surjective | exact etale_bockstein_reduction_kernel_eq_image | exact etale_bockstein_twisted_short_exact_sequence | exact etale_bockstein_restriction_of_resolution | exact etale_bockstein_connecting_map_unique_up_to_sign | exact etale_bockstein_reduction_postcomposition_compat | exact etale_torsion_cohomology_primary_part_basic | exact etale_torsion_cohomology_primary_localization | exact etale_torsion_cohomology_twist_section | exact etale_torsion_cohomology_mono_epi_of_exact | exact etale_sheaf_short_complex_exact_iff_locally_lifts | exact etale_torsion_cohomology_localization_basic | exact etale_torsion_cohomology_residue_basic | exact etale_torsion_cohomology_extension_hom_exists | exact etale_torsion_cohomology_operation_spec | exact etale_torsion_cohomology_operation_comp | exact etale_prime_power_twist_reduction_map_exists | exact etale_prime_power_twist_restriction_exists
end LateralTheory.Fin.AdicFin
end

section -- merged from Development.EtaleCohomology.WeilConjectures.FinQCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.FinQCut

theorem inv_of_over {q : ℕ} {A : Type} [CommRing A] (hq : IsUnit (q : A)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of A)) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have f : U ⟶ X := x
  have h := hq.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (f ≫ p).appTop).hom)
  rwa [map_natCast] at h

end LateralTheory.EWeil.FinQCut

end
end

section -- merged from Development.EtaleCohomology.WeilConjectures.AdicKerPf
noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC LateralTheory.KummerTheory

namespace LateralTheory.EWeil.AdicKerPf

theorem nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem comp (hA : A11) {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (y : Hl l E n i) (M m : ℕ) (h : m ≤ M) :
    red (l ^ M) (l ^ m) E n i (y.1 M) = y.1 m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => haveI := nz l m; exact (hA (l ^ m) (l ^ m) dvd_rfl E).2.2.1 n i (y.1 m)
  | succ d ih =>
    haveI := nz l (m + (d + 1))
    rw [← (hA (l ^ (m + (d + 1))) (l ^ (m + d)) (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (y.1 _)]
    rw [show red (l ^ (m + (d + 1))) (l ^ (m + d)) E n i (y.1 (m + (d + 1))) = y.1 (m + d) from y.2 (m + d)]
    exact ih

theorem smul_pow {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (m b : ℕ) (v : HtL l m E n i) :
    ((l : ℤ_[l]) ^ b) • v = (show Ht (l ^ m) E n i from (l ^ b : ℕ) • v) := by
  change PadicInt.toZModPow m ((l : ℤ_[l]) ^ b) • (show Ht (l ^ m) E n i from v) = _
  rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

theorem AdicKer_of : LateralTheory.KummerTheory.AdicKer := by
  intro hA l _ E i hB hFin n b x hx
  change x.1 b = 0 at hx
  obtain ⟨u, d, hBk⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  let f : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (hBk a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := S) fun a => TypeCat.ofHom (f a)
  haveI : ∀ j, Finite (F.obj j) := fun j => by
    haveI := hFin j.unop n
    exact (inferInstance : Finite (S j.unop))
  haveI : ∀ j, Nonempty (F.obj j) := fun j => by
    have h0 : red (l ^ (b + j.unop)) (l ^ b) E n i (x.1 (b + j.unop)) = 0 := by
      rw [comp hA x (b + j.unop) b (by omega)]; exact hx
    obtain ⟨w, hw⟩ := ((hBk j.unop n).1 (x.1 (b + j.unop))).1 h0
    exact ⟨(⟨w, hw⟩ : S j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let y : Hl l E n i := ⟨fun a => (show S a from s (op a)).1, fun a => by
    have := hs (homOfLE (Nat.le_succ a)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this⟩
  refine ⟨y, Subtype.ext (funext fun m => ?_)⟩
  change x.1 m = ((l : ℤ_[l]) ^ b) • y.1 m
  rw [smul_pow]
  rcases le_or_gt m b with h | h
  · have hxm : x.1 m = 0 := by
      rw [← comp hA x b m h]
      exact (congrArg (red (l ^ b) (l ^ m) E n i) hx).trans (map_zero _)
    rw [hxm]
    obtain ⟨c, hc⟩ := pow_dvd_pow l h
    change 0 = (l ^ b : ℕ) • (show Ht (l ^ m) E n i from y.1 m)
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ m)), hc, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_smul]
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have h1 : u a n (y.1 a) = x.1 (b + a) := (show S a from s (op a)).2
    rw [← h1, ← comp hA y (b + a) a (by omega)]
    exact (hBk a n).2.2.2.1 (y.1 (b + a))

end LateralTheory.EWeil.AdicKerPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAicLocalSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosed
open GlobalTheory.EtC

namespace GlobalTheory

theorem integralClosure_maximal_residue_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  intro k K _ _ _ φ D m₀ hφD hm₀ hres hfrac
  let A := integralClosure D K
  have hφA : ∀ c : k, φ c ∈ A := fun c =>
    isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))
  have hker : RingHom.ker (algebraMap D A) ≤ m₀ := by
    intro d hd
    have h0 : (algebraMap D A d : K) = 0 := by rw [RingHom.mem_ker.mp hd]; rfl
    have : d = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨𝔪, h𝔪max, h𝔪comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker
  let φA : k →+* A := φ.codRestrict A hφA
  let ψ : k →+* A ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp φA
  have hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ := by
    intro d
    obtain ⟨c, hc, hdc⟩ := hres d
    refine ⟨c, ?_⟩
    have hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪 := by
      rw [← Ideal.mem_comap]
      change d - ⟨φ c, hc⟩ ∈ Ideal.under D 𝔪
      rw [h𝔪comap]
      exact hdc
    change Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)
    symm
    rw [map_sub] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪 := by
    intro r
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra
    have hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r) :=
      (Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)
    obtain ⟨f, hfm, hf⟩ := hr
    have hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; rw [Polynomial.coeff_map]; exact hcoef _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)
    have hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r) := by
      refine ⟨q, hqm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change Polynomial.eval _ (q.map ψ) = 0
      rw [hq, ← Polynomial.eval₂_eq_eval_map]
      exact hf
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _ h1
    exact ⟨c, Ideal.Quotient.eq.mp hc.symm⟩
  refine ⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩; exact hφA c
  · intro r
    obtain ⟨c, hc⟩ := hres' r
    exact ⟨c, hφA c, hc⟩
  · intro x
    obtain ⟨d, hd, hint⟩ := hfrac x
    refine ⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩
    intro h
    apply hd
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro x hx
    have hx' : IsIntegral A x := hx
    exact isIntegral_trans x hx'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosedStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_maximal_residue_of_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  first | exact @GlobalTheory.integralClosure_maximal_residue_algClosed | exact GlobalTheory.integralClosure_maximal_residue_algClosed | (intros; apply GlobalTheory.integralClosure_maximal_residue_algClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
open GlobalTheory.EtC

namespace GlobalTheory

theorem exists_polySubring_maximal_integral (k K : Type) [Field k] [Field K] (φ : k →+* K) :
    ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧
      ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  letI : Algebra k K := φ.toAlgebra
  haveI : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 φ.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  set A : Subalgebra k K := Algebra.adjoin k (Set.range ((↑) : s → K)) with hA
  let ε : A →ₐ[k] k := (MvPolynomial.aeval (fun _ : s => (0 : k))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hε : ∀ c : k, ε (algebraMap k A c) = c := fun c => ε.commutes c
  let D : Subring K := A.toSubring
  let εD : D →+* k := (ε : A →+* k)
  have hεs : Function.Surjective εD := fun c => ⟨algebraMap k A c, hε c⟩
  refine ⟨D, RingHom.ker εD, ?_, RingHom.ker_isMaximal_of_surjective εD hεs, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact A.algebraMap_mem c
  · intro r
    refine ⟨εD r, A.algebraMap_mem _, ?_⟩
    rw [RingHom.mem_ker, map_sub]
    have : εD ⟨φ (εD r), A.algebraMap_mem _⟩ = εD r := hε (εD r)
    rw [this, sub_self]
  · intro x
    haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
    haveI : Algebra.IsAlgebraic D K := ‹Algebra.IsAlgebraic A K›
    obtain ⟨y, hy, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_integral_multiple
    exact ⟨y, hy, by rwa [Algebra.smul_def] at hint⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegralStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialSubring_maximal_integral : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧ ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  first | exact @GlobalTheory.exists_polySubring_maximal_integral | exact GlobalTheory.exists_polySubring_maximal_integral | (intros; apply GlobalTheory.exists_polySubring_maximal_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidue
noncomputable section

open GlobalTheory.EtC

namespace GlobalTheory.LocInField

variable {K : Type} [Field K]

def locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : Subring K where
  carrier := {x | ∃ a s : R, s ∉ 𝔪 ∧ x * s = a}
  zero_mem' := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  one_mem' := ⟨1, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * t + b * s, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * b, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast; rw [← hx]; ring

theorem le_locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : R ≤ locAt R 𝔪 := fun x hx =>
  ⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩

theorem exists_local_subring : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  intro k K _ _ _ φ R 𝔪 hφ hmax hres hden hic
  haveI : 𝔪.IsPrime := hmax.isPrime
  have hRT := le_locAt R 𝔪
  letI : Algebra R (locAt R 𝔪) := (Subring.inclusion hRT).toAlgebra
  haveI : IsScalarTower R (locAt R 𝔪) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : ∀ s : R, s ∉ 𝔪 → IsUnit (algebraMap R (locAt R 𝔪) s) := by
    intro s hs
    have hs0 : (s : K) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact zero_mem _)
    refine isUnit_iff_exists_inv.2 ⟨⟨(s : K)⁻¹, 1, s, hs, by simp [hs0]⟩, Subtype.ext ?_⟩
    change (s : K) * (s : K)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  haveI hloc : IsLocalization 𝔪.primeCompl (locAt R 𝔪) :=
    { map_units := fun s => hunit s s.2
      surj := fun t => by
        obtain ⟨a, s, hs, h⟩ := t.2
        exact ⟨(a, ⟨s, hs⟩), Subtype.ext h⟩
      exists_of_eq := fun {x y} h => by
        have h' := congrArg Subtype.val h
        have hxy : x = y := Subtype.ext h'
        exact ⟨1, by rw [hxy]⟩ }
  haveI : IsLocalRing (locAt R 𝔪) := IsLocalization.AtPrime.isLocalRing (locAt R 𝔪) 𝔪
  refine ⟨locAt R 𝔪, fun x hx => hRT (hφ hx), ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · intro p hp hdeg
    have hdeg' : (p.map (algebraMap (locAt R 𝔪) K)).degree ≠ 0 := by
      rw [hp.degree_map, Polynomial.degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hyT : IsIntegral (locAt R 𝔪) y := ⟨p, hp, by rw [← Polynomial.eval_map]; exact hy⟩
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl y hyT
    have hmR : m • y ∈ R := hic _ hm
    have hmy : m • y = y * ((m : R) : K) := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_comm]; rfl
    have hyT' : y ∈ locAt R 𝔪 := ⟨⟨m • y, hmR⟩, m, m.2, hmy.symm⟩
    refine ⟨⟨y, hyT'⟩, Subtype.ext ?_⟩
    change algebraMap (locAt R 𝔪) K (p.eval ⟨y, hyT'⟩) = 0
    rw [← Polynomial.eval₂_at_apply (algebraMap (locAt R 𝔪) K), ← Polynomial.eval_map]
    exact hy
  · intro t
    obtain ⟨a, s, hs, hts⟩ := t.2
    obtain ⟨c, hc, hac⟩ := hres a
    obtain ⟨e, he, hse⟩ := hres s
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hs
      have h0 : s - ⟨φ 0, he⟩ = s := by
        rw [sub_eq_self]; exact Subtype.ext (by simp)
      rwa [h0] at hse
    have hg : φ (c / e) ∈ R := hφ ⟨c / e, rfl⟩
    have hge : φ (c / e) * φ e = φ c := by rw [← map_mul, div_mul_cancel₀ c he0]
    refine ⟨c / e, hRT hg, ?_⟩
    have hb : (a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩) ∈ 𝔪 :=
      sub_mem hac (Ideal.mul_mem_left _ _ hse)
    have key : (t - ⟨φ (c / e), hRT hg⟩) * algebraMap R (locAt R 𝔪) s =
        algebraMap R (locAt R 𝔪) ((a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩)) := by
      apply Subtype.ext
      change ((t : K) - φ (c / e)) * (s : K) = ((a : K) - φ c) - φ (c / e) * ((s : K) - φ e)
      linear_combination hts - hge
    have hb' := (IsLocalization.AtPrime.to_map_mem_maximal_iff (locAt R 𝔪) 𝔪 _).2 hb
    rw [← key] at hb'
    exact (Ideal.IsPrime.mem_or_mem inferInstance hb').resolve_right
      fun h => (IsLocalRing.mem_maximalIdeal _).1 h (hunit s hs)
  · haveI : FaithfulSMul (locAt R 𝔪) K := inferInstance
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨d, hd, hdz⟩ := hden z
    have hd0 : (d : K) ≠ 0 := fun h => hd (Subtype.ext h)
    refine ⟨⟨(d : K) * z, hRT hdz⟩, ⟨d, hRT d.2⟩, ?_⟩
    change z = (d : K) * z / d
    field_simp

end GlobalTheory.LocInField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidueStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_subring_monic_roots_residue : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  first | (exact @GlobalTheory.LocInField.exists_local_subring) | (exact GlobalTheory.LocInField.exists_local_subring) | (intros; apply GlobalTheory.LocInField.exists_local_subring  <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem exists_aic_local_subring (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] (φ : k →+* K) :
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  obtain ⟨D, m₀, hD, hm₀, hres, hint⟩ := GlobalTheory.T.exists_polynomialSubring_maximal_integral k K φ
  obtain ⟨R, 𝔪, hR, h𝔪, hres', hfr, hic⟩ := GlobalTheory.T.integralClosure_maximal_residue_of_algClosed k K φ D m₀ hD hm₀ hres hint
  exact GlobalTheory.T.exists_local_subring_monic_roots_residue k K φ R 𝔪 hR h𝔪 hres' hfr hic

section Eqv
variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_trans {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_of_eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := by
  intro n
  have h : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun x y hxy => (hfg n).1 (by rw [h, h, hxy]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hfg n).2 (pull R f F n y)
  exact ⟨x, (hf n).1 (by rw [← h, hx])⟩

variable {X Y W S : Scheme.{0}} (p : X ⟶ S) (d : Y ⟶ S) (g : W ⟶ Y)

theorem fst_comp_eq : pullback.fst p (g ≫ d) =
    (pullbackLeftPullbackSndIso p d g).inv ≫ pullback.fst (pullback.snd p d) g ≫ pullback.fst p d := by
  rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_fst]

theorem eqv_fst_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p d)) F) : Eqv R (sch.map (pullback.fst p (g ≫ d))) F := by
  rw [fst_comp_eq, Functor.map_comp, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) (eqv_trans F h1 h2)

theorem eqv_fst_of_comp (h1 : Eqv R (sch.map (pullback.fst (pullback.snd p d) g)) F)
    (h2 : Eqv R (sch.map (pullback.fst p (g ≫ d))) F) : Eqv R (sch.map (pullback.fst p d)) F := by
  refine eqv_of_eqv_comp F h1 ?_
  have : pullback.fst (pullback.snd p d) g ≫ pullback.fst p d =
      (pullbackLeftPullbackSndIso p d g).hom ≫ pullback.fst p (g ≫ d) := by
    rw [pullbackLeftPullbackSndIso_hom_fst]
  rw [← Functor.map_comp, this, Functor.map_comp]
  exact eqv_trans F (eqv_iso F _) h2

end Eqv

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem eqv_fieldChange (hE2 : E2) (hE3 : E3) (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K]
    [IsAlgClosed K] (φ : k →+* K) (hq : IsUnit (q : k)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) (tw q i) := by
  obtain ⟨T, hφT, ⟨hloc, hT, hres⟩, hfr⟩ := exists_aic_local_subring k K φ
  let α : k →+* T := φ.codRestrict T (fun c => hφT ⟨c, rfl⟩)
  have hqT : IsUnit (q : T) := by simpa using hq.map α
  let a := Spec.map (CommRingCat.ofHom α)

  have hb : Function.Bijective ((IsLocalRing.residue T).comp α) := by
    refine ⟨(IsLocalRing.residue T).comp α |>.injective, fun y => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, h, hc⟩ := hres t
    refine ⟨c, ?_⟩
    change IsLocalRing.residue T (α c) = IsLocalRing.residue T t
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have e : α c - t = -(t - ⟨φ c, h⟩) := by rw [neg_sub]; rfl
    rw [e]
    exact (IsLocalRing.maximalIdeal T).neg_mem hc
  haveI : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue T))
  have hra : r ≫ a = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp α)) := (spec_comp _ _).symm
  have hsp : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a) r)) (tw q i) :=
    eqv_spInc hE2 hT q hqT (pullback.snd p a) i
  have hXT : Eqv (ZMod q) (sch.map (pullback.fst p a)) (tw q i) := by
    refine eqv_fst_of_comp _ p a r hsp ?_
    rw [hra]
    exact eqv_iso _ _

  let e := IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K
  have hφ : φ = (e.toRingEquiv.toRingHom).comp ((algebraMap T (FractionRing T)).comp α) := by
    ext c
    simp only [RingHom.comp_apply]
    rw [show e.toRingEquiv.toRingHom (algebraMap T (FractionRing T) (α c)) = e (algebraMap T (FractionRing T) (α c)) from rfl,
      AlgEquiv.commutes]
    rfl
  haveI : IsIso (CommRingCat.ofHom (e.toRingEquiv.toRingHom)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have hgen : Eqv (ZMod q) (sch.map (pullback.fst (pullback.snd p a)
      (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i) :=
    eqv_genInc hE3 hT q hqT (pullback.snd p a) i
  rw [hφ, spec_comp, spec_comp]
  refine eqv_fst_comp _ p _ _ (eqv_iso _ _) (eqv_fst_comp _ p a _ hgen hXT)

end GlobalTheory.GenusTwoPureComparison.Cmp
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JVBcS
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jVBcS :
    VBcS := by
  intro l _ k Ω _ _ _ _ φ hl X p _ _ n i
  refine GlobalTheory.GenusTwoPureComparison.Cmp.pullHQ_bijective l _ n i fun m => ?_
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ m : ℕ) : k) := by
    push_cast
    exact hl.pow m
  exact GlobalTheory.GenusTwoPureComparison.Cmp.eqv_fieldChange UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality (l ^ m) k Ω φ hq p i n
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.VFinHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.G3

theorem vFin_holds : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hT : ∀ a m, Finite (Ht (l ^ a) (sch.obj X) m i) := fun a m => by
    have : NeZero (l ^ a) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact UpperTheory.Et.etale_finiteness_of_duality (l ^ a) k (by rw [Nat.cast_pow]; exact hl.pow a) p m i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l _ n i (fun a => hT a n)
      (LateralTheory.EWeil.AdicKerPf.AdicKer_of GlobalTheory.EtC.RedCoef.a11 l _ i
        (fun b => LateralTheory.Fin.AdicFin.etale_bockstein_sequence_adic_finiteness GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 l b _ i
          (LateralTheory.EWeil.FinQCut.inv_of_over hl p)) hT n)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCorrUniq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem htot_subsingleton (l : ℕ) [Fact l.Prime] (E : Spc)
    (h : ∀ n : ℤ, Subsingleton (Hl l E n 0)) : Subsingleton (Htot l E) := by
  have hq : ∀ n : ℤ, Subsingleton (HQ l E n 0) := fun n => by
    have := h n
    refine ⟨fun a b => ?_⟩
    have z : ∀ c : HQ l E n 0, c = 0 := fun c => by
      induction c using TensorProduct.induction_on with
      | zero => rfl
      | tmul q y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add c d hc hd => rw [hc, hd, add_zero]
    rw [z a, z b]
  exact ⟨fun a b => DFinsupp.ext fun n => (hq n).elim _ _⟩

private theorem op_eq (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (p : Z ⟶ sp k)
    (s : Y ⟶ Z) (t : Y ⟶ Z') (hT : (et l (sp k)).Good)
    (tr : (et l (sp k)).H (s ≫ p) →ₗ[ℚ_[l]] (et l (sp k)).H p) (htr : (et l (sp k)).IsTr p (s ≫ p) s tr)
    (A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (hA : IsCorrOp l s t A)
    (x : Htot l (sch.obj Z')) : A x = tr (pullTot l (sch.map t) x) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, hx⟩ := hA
  have hσ : ∀ j, σ j ≫ s ≫ p = c ≫ p := fun j => by
    rw [← Category.assoc, hsp.choose j]
  have hinj := hT.inj p (c ≫ p) c rfl G a hgal
  apply hinj
  have e := htr W (c ≫ p) c rfl J σ hσ hsp (pullTot l (sch.map t) x)
  refine Eq.trans ?_ e.symm
  refine (hx x).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Functor.map_comp, pullTot_comp]
  rfl

theorem UpperTheory.Gal.G3.jCorrUniq :
    EtGood → SplitDesc → CharVan → CorrUniq := by
  intro hG hD hV l _ k _ Z Y Z' p s t A A' hA hA'
  by_cases hl : (l : k) = 0
  · have := htot_subsingleton l (sch.obj Z) fun n => hV l k hl p n 0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · have hu : IsUnit (l : Γ(sp k, ⊤)) := by
      have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (l : k)) := (IsUnit.mk0 _ hl).map _
      rwa [map_natCast] at h
    have hT := hG l (sp k) hu
    obtain ⟨W, c, G, _, _, a, J, _, σ, hgal, hsp, -⟩ := id hA
    obtain ⟨hf, he, hs, -, -, -⟩ := hgal
    obtain ⟨_, _⟩ := @hD Z Y W s c hf he hs J _ σ hsp
    obtain ⟨tr, htr⟩ := hT.tr p (s ≫ p) s rfl
    exact LinearMap.ext fun x => (op_eq l k p s t hT tr htr A hA x).trans (op_eq l k p s t hT tr htr A' hA' x).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCharVan
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.G3

private theorem prim_isEmpty {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {V : Scheme.{0}} (v : V) (f : V ⟶ sp k) :
    IsEmpty (Prim q Γ(V, ⊤)) := by
  constructor
  rintro ⟨ζ, hu, -⟩
  have h0 : ((q : ℕ) : Γ(sp k, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom,
      show ((q : ℕ) : CommRingCat.of k) = 0 from hq, map_zero]
  have h1 : ((q : ℕ) : Γ(V, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, h0, map_zero]
  rw [h1] at hu
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  exact not_isUnit_zero hu

private theorem sec_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) (i : ℤ) {U : Scheme.{0}} (f : U ⟶ sp k) :
    Subsingleton (Sec (tw q i) U) := by
  suffices h : ∀ x : Sec (tw q i) U, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  let S : Sieve U :=
    { arrows := fun V j => Sec.res j x = 0
      downward_closed := by
        intro V W j hj g
        have hj' : ModuleCat.Hom.hom ((tw q i).obj.map j.op) x = 0 := hj
        show ModuleCat.Hom.hom ((tw q i).obj.map (g ≫ j).op) x = 0
        rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hj', map_zero] }
  have hS : S ∈ Scheme.etaleTopology U := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨V, j, v, m, -, hj, hv, hm⟩ := (GlobalTheory.ofRings_loc (ZMod q) (twF q i) U).1 x u
    refine ⟨V, j, v, hj, hv, ?_⟩
    refine hm.symm.trans ?_
    haveI : IsEmpty (Prim q Γ(V, ⊤)) := prim_isEmpty hq v (j ≫ f)
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q i Γ(V, ⊤)) m
    rw [Subsingleton.elim g 0, Submodule.Quotient.mk_zero]
    exact map_zero _
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (J := Scheme.etaleTopology) (P' := (tw q i).obj)
      (forget (ModuleCat.{1} (ULift.{1, 0} (ZMod q))))).mp (tw q i).property)
  exact (hsh S hS).isSeparatedFor (fun _ _ _ => 0) x 0 (fun V j hj => hj)
    (fun V j hj => show ModuleCat.Hom.hom ((tw q i).obj.map j.op) 0 = 0 from map_zero _)

private theorem ht_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {X : Scheme.{0}} (p : X ⟶ sp k) (n i : ℤ) :
    Subsingleton (Ht q (sch.obj X) n i) := by
  have hbij := GlobalTheory.T.etaleCohomology_bijective_of_support_bijective (ZMod q) (sch.obj X) (0 : tw q i ⟶ tw q i) (fun U hU => by
    obtain ⟨g⟩ := hU
    have g' : U ⟶ X := g
    haveI := sec_subsingleton hq i (g' ≫ p)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩) n
  have hz : HK.post (ZMod q) ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) n = 0 := by
    have h := PostFun.post_add ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) 0 n
    rw [add_zero] at h
    exact left_eq_add.1 h
  refine ⟨fun a b => hbij.1 ?_⟩
  rw [hz]; rfl

theorem jCharVan : CharVan := by
  intro l _ k _ hl X x n i
  have hs : ∀ m : ℕ, Subsingleton (Ht (l ^ (m + 1)) (sch.obj X) n i) := fun m =>
    ht_subsingleton (k := k) (by push_cast; rw [hl, zero_pow (Nat.succ_ne_zero m)]) x n i
  constructor
  intro a b
  apply Subtype.ext
  funext m
  cases m with
  | zero =>
    rw [← a.2 0, ← b.2 0]
    congr 1
    exact (hs 0).elim _ _
  | succ m => exact (hs m).elim _ _

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JSplitDesc
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3 MorphismProperty
universe u v

set_option backward.isDefEq.respectTransparency.types false in
private theorem isProper_desc {A G U Z : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hUC : UniversallyClosed g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))
  have hLFT : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))
  have hD : MorphismProperty.diagonal @UniversallyClosed g := by
    refine of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  rw [MorphismProperty.diagonal_iff] at hD
  have hP : IsProper (pullback.diagonal g) := IsProper.mk
  have hC : IsClosedImmersion (pullback.diagonal g) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩
  haveI : IsSeparated g := ⟨hC⟩
  exact IsProper.mk

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc_fin (W : Scheme.{0}) (n : ℕ) :
    IsFinite (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
  induction n with
  | zero =>
    haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm
    infer_instance
  | succ n ih =>
    let t := extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W)
      (coprodIsCoprod W (∐ fun _ : Fin n => W))
    let e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W) :=
      (coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t
    have key : (Sigma.desc (f := fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) =
        e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have hj := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [hj]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]
        exact (coprod.inl_desc _ _).symm
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ]
        show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫
          coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)
        rw [Category.assoc, coprod.inr_desc, Sigma.ι_desc]
    rw [key]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc (W : Scheme.{0}) (J : Type) [Finite J] :
    IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have key : (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) =
      (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, ← Category.assoc]
    have h := Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    exact (Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm
  rw [key]
  haveI := isFinite_desc_fin W n
  infer_instance

private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  have hf : affineLocally RingHom.Etale f := by
    rw [← HasRingHomProperty.eq_affineLocally @Etale]
    exact ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf
  letI : Algebra R S := RingHom.toAlgebra g
  have : Algebra.Etale R S := hg
  show Algebra.QuasiFinite R S
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
theorem UpperTheory.Gal.G3.jSplitDesc :
    SplitDesc := by
  intro Z Y W s c _ _ _ J _ σ hs
  obtain ⟨hσ, hiso⟩ := hs
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have key : pullback.snd s c =
      inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫
        Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]
  haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J
  haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance
  haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance
  have hpb := IsPullback.of_hasPullback s c
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : IsProper s := isProper_desc hpb
  have hE : Etale s := of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))
  haveI := hE
  haveI := locallyQuasiFinite_of_etale s
  exact ⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩
end

namespace UpperTheory.Gal.G3

theorem etnGood' : EtnGood := pEtnGood (pFEtBasic pPtsOfSplits) pEtTr

theorem corrUniq_holds : CorrUniq := jCorrUniq (pEtGood etnGood') jSplitDesc jCharVan

theorem vBcS_holds : VBcS := jVBcS

theorem vInv_holds : GlobalTheory.GalV.VInv := fun l _ _ _ f _ _ _ G _ a ha hiso n i => GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants l f G a ha hiso n i

end UpperTheory.Gal.G3
