module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HeckeCharacterEqOfCofinite

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegSquarePadic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_primes_neg_square_padic : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  first | exact @GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare | exact GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare | (intros; apply GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DecompositionFixesSquareRoot
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SqrtFixedOfIsSquarePadic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqFix

theorem exists_int_sq_approx (q : ℕ) [Fact q.Prime] (d : ℤ) (h : IsSquare (d : ℚ_[q])) (n : ℕ) :
    ∃ x : ℤ, ((q : ℤ) ^ n) ∣ d - x ^ 2 := by
  obtain ⟨y, hy⟩ := h
  have hy1 : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ * ‖y‖ ≤ 1 := by
      rw [← norm_mul, ← hy]; exact Padic.norm_int_le_one d
    nlinarith [norm_nonneg y]
  set y' : ℤ_[q] := ⟨y, hy1⟩ with hy'
  set x : ℤ := ((PadicInt.toZModPow n y').val : ℤ) with hx
  refine ⟨x, ?_⟩
  have hmem : y' - (x : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]
    simp
  have hd : ((d : ℤ) : ℤ_[q]) = y' * y' := by
    apply Subtype.ext
    simp [hy', hy]
    rfl
  have hmem2 : (((d - x ^ 2 : ℤ)) : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    have : (((d - x ^ 2 : ℤ)) : ℤ_[q]) = (y' - (x : ℤ_[q])) * (y' + (x : ℤ_[q])) := by
      push_cast; rw [hd]; ring
    rw [this]; exact Ideal.mul_mem_right _ _ hmem
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hmem2
  exact_mod_cast (PadicInt.norm_int_le_pow_iff_dvd (p := q)).mp this

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem valuation_apply_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (s : G F Ω) (hs : s ∈ Dec (F := F) A) (z w : Ω)
    (h : A.valuation z ≤ A.valuation w) : A.valuation (s z) ≤ A.valuation (s w) := by
  by_cases hw : w = 0
  · subst hw
    have hz : z = 0 := by
      have : A.valuation z = 0 := le_antisymm (by simpa using h) zero_le'
      simpa using this
    subst hz; simp
  · have hsw : s w ≠ 0 := (map_ne_zero_iff _ s.injective).mpr hw
    have h1 : A.valuation (z / w) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le'
    have h2 : s (z / w) ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hs _).mpr ((A.valuation_le_one_iff _).mp h1)
    rw [map_div₀] at h2
    have h3 := (A.valuation_le_one_iff _).mpr h2
    rw [map_div₀] at h3
    have hv : A.valuation (s w) ≠ 0 := by simpa using hsw
    exact (div_le_one₀ (zero_lt_iff.mpr hv)).mp h3

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem sqrt_fixed_of_isSquare_padic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (q : ℕ) [Fact q.Prime], ((q : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ (d : ℤ) (δ : Ω), δ ^ 2 = (d : Ω) → IsSquare (d : ℚ_[q]) → ∀ s ∈ Dec (F := F) A, s δ = δ := by
  intro F Ω _ _ _ _ _ v A hA q _ hq d δ hδ hsq s hs
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsδ2 : s δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_intCast]
  by_cases hd : d = 0
  · subst hd
    have : δ = 0 := by simpa using hδ
    subst this; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsδ2 with h | h
  · exact h
  exfalso
  have hqv : A.valuation (q : Ω) < 1 := by
    have := (hA (q : 𝓞 F)).mpr hq
    simpa using this
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hN0 : (4 * d).natAbs ≠ 0 := by simp [hd]
  obtain ⟨k, u, hu, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 q (Fact.out : q.Prime).one_lt.ne'
  have hV4d : A.valuation (((4 * d : ℤ)) : Ω) = A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := by
    rcases Int.natAbs_eq (4 * d) with e | e
    · rw [e, hN]; push_cast; rw [map_mul, map_pow]
    · rw [e, hN]; push_cast; rw [Valuation.map_neg, map_mul, map_pow]
  have hu1 : 1 ≤ A.valuation (u : Ω) := by
    refine not_lt.mp fun hlt => ?_
    have hu' : ((u : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA (u : 𝓞 F)).mp (by simpa using hlt)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu)
    have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at e
      rw [← e]
      exact add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hu')
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨x, m, hm⟩ := exists_int_sq_approx q d hsq (k + 1)
  set a : Ω := δ - x with ha
  set b : Ω := δ + x with hb
  have hab : a * b = (q : Ω) ^ (k + 1) * (m : Ω) := by
    have e := congrArg (Int.cast : ℤ → Ω) hm
    push_cast at e
    rw [ha, hb, ← e, ← hδ]; ring
  have hsa : s a = -b := by rw [ha, hb, map_sub, map_intCast, h]; ring
  have hsb : s b = -a := by rw [ha, hb, map_add (f := _), map_intCast, h]; ring
  have hVab : A.valuation a = A.valuation b := by
    rcases le_total (A.valuation a) (A.valuation b) with e | e
    · refine le_antisymm e ?_
      have := valuation_apply_le A s hs a b e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
    · refine le_antisymm ?_ e
      have := valuation_apply_le A s hs b a e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
  have hm1 : A.valuation (m : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hVa : A.valuation a * A.valuation a ≤ A.valuation (q : Ω) ^ (k + 1) := by
    calc A.valuation a * A.valuation a = A.valuation (a * b) := by rw [map_mul, hVab]
      _ = A.valuation (q : Ω) ^ (k + 1) * A.valuation (m : Ω) := by rw [hab, map_mul, map_pow]
      _ ≤ A.valuation (q : Ω) ^ (k + 1) * 1 := mul_le_mul' le_rfl hm1
      _ = _ := mul_one _
  have h2δ : A.valuation (2 * δ) ≤ A.valuation a := by
    have e : 2 * δ = a + b := by rw [ha, hb]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [hVab, max_self]
  have h4d : A.valuation (((4 * d : ℤ)) : Ω) ≤ A.valuation (q : Ω) ^ (k + 1) := by
    have e : (((4 * d : ℤ)) : Ω) = (2 * δ) * (2 * δ) := by push_cast; rw [← hδ]; ring
    rw [e, map_mul]
    exact (mul_le_mul' h2δ h2δ).trans hVa
  have hqk : A.valuation (q : Ω) ^ k ≠ 0 := pow_ne_zero _ (by simpa using hq0)
  have key : A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (q : Ω) := by
    calc A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := mul_le_mul' le_rfl hu1
      _ = A.valuation (((4 * d : ℤ)) : Ω) := hV4d.symm
      _ ≤ A.valuation (q : Ω) ^ (k + 1) := h4d
      _ = _ := pow_succ _ _
  have h3 := mul_le_mul' (le_refl (A.valuation (q : Ω) ^ k)⁻¹) key
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hqk, one_mul, one_mul] at h3
  have := h3
  exact absurd hqv (not_lt.mpr this)

end GlobalTheory.SqFix
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_fixes_square_root : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (q : ℕ) [Fact q.Prime], ((q : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ (d : ℤ) (δ : Ω), δ ^ 2 = (d : Ω) → IsSquare (d : ℚ_[q]) → ∀ s ∈ Dec (F := F) A, s δ = δ := by
  first | exact @GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic | exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic | (intros; apply GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaMovesSquareRoot
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SqrtNegMovedByInertia
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem valuation_natCast_eq {F : Type} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr F) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) := by
  have h2 := GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr hp hd v hv
  have e : (p : F) = algebraMap (𝓞 F) F (p : 𝓞 F) := by simp
  rw [e, v.valuation_of_algebraMap]
  have h0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne := v.intValuation_ne_zero _ h0
  have h1 := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
  have h2' := mt (v.intValuation_le_pow_iff_mem _ 2).1 h2
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  rw [WithZero.exp_inj]
  push_cast at h1 h2'
  omega

theorem valuation_mul_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) {δ : Ω}
    (hδ : δ ^ 2 = -(p : Ω)) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) (y : F) (hy : y ≠ 0) :
    A.valuation (algebraMap F Ω y * δ) ≠ 1 := by
  intro h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  have hmem : ∀ e : F, algebraMap F Ω e ∈ A ↔ v.valuation F e ≤ 1 := fun e => by
    rw [hι, ι.commutes]; exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff v e
  have he : algebraMap F Ω (y ^ 2 * p) = -(algebraMap F Ω y * δ) ^ 2 := by
    rw [mul_pow, hδ, map_mul, map_pow, map_natCast]; ring
  have hw : A.valuation (algebraMap F Ω (y ^ 2 * p)) = 1 := by
    rw [he, Valuation.map_neg, map_pow, h, one_pow]
  have h1 : v.valuation F (y ^ 2 * p) ≤ 1 := (hmem _).1 ((A.valuation_le_one_iff _).1 hw.le)
  have h2 : v.valuation F (y ^ 2 * p)⁻¹ ≤ 1 :=
    (hmem _).1 ((A.valuation_le_one_iff _).1 (by rw [map_inv₀, map_inv₀, hw, inv_one]))
  have hy0 : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_inv₀] at h2
  rw [map_mul, map_pow, valuation_natCast_eq hp hd v hv, ← WithZero.exp_log hy0,
    ← WithZero.exp_nsmul, ← WithZero.exp_add] at h1 h2
  rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  omega

end GlobalTheory.SqrtNegRam

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem sqrt_neg_moved_by_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ discr F → ∀ (δ : Ω), δ ^ 2 = -(p : Ω) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ s ∈ Ine (F := F) A, s δ ≠ δ := by
  intro F Ω _ _ _ _ _ p hp _ hd δ hδ v A hv hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have KL := valuation_mul_ne_one hp hd hδ hv hA
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    apply hp0
    linear_combination hδ
  set f : F[X] := X ^ 2 + C (p : F) with hfdef
  have hf_root : ∀ x : Ω, aeval x f = 0 ↔ x ^ 2 = -(p : Ω) := by
    intro x
    simp only [hfdef, map_add (f := _), map_pow, aeval_X, aeval_C, map_natCast]
    constructor <;> intro h <;> linear_combination h
  have hmon : f.Monic := monic_X_pow_add_C _ two_ne_zero
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hfdef, natDegree_X_pow_add_C]; decide
    · intro c hc
      have hc' : (algebraMap F Ω c) ^ 2 = -(p : Ω) := by
        rw [← hf_root, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hc, map_zero]
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hp0
        rw [map_zero] at hc'
        linear_combination hc'
      have hc1 : (algebraMap F Ω c)⁻¹ * algebraMap F Ω c = 1 :=
        inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hc0)
      have hfac : (algebraMap F Ω c - δ) * (algebraMap F Ω c + δ) = 0 := by
        linear_combination hc' - hδ
      rcases mul_eq_zero.1 hfac with h | h
      · apply KL c⁻¹ (inv_ne_zero hc0)
        rw [map_inv₀, ← sub_eq_zero.1 h, hc1, map_one]
      · apply KL c⁻¹ (inv_ne_zero hc0)
        have e : δ = -(algebraMap F Ω c) := by linear_combination h
        rw [e, mul_neg, map_inv₀, hc1, Valuation.map_neg, map_one]
  have hmin : f = minpoly F δ := minpoly.eq_of_irreducible_of_monic hirr ((hf_root δ).2 hδ) hmon
  have hmin' : f = minpoly F (-δ) :=
    minpoly.eq_of_irreducible_of_monic hirr ((hf_root _).2 (by rw [neg_sq]; exact hδ)) hmon
  obtain ⟨σ₀, hσ₀⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 (hmin'.symm.trans hmin)
  have hσ₀' : σ₀ δ = -δ := hσ₀
  let M : IntermediateField F Ω := IntermediateField.adjoin F (f.rootSet Ω)
  haveI : Polynomial.IsSplittingField F M f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : Normal F M := Normal.of_isSplittingField f
  haveI : FiniteDimensional F M := Polynomial.IsSplittingField.finiteDimensional M f
  haveI : IsGalois F M := ⟨⟩
  let τ : M ≃ₐ[F] M := σ₀.restrictNormal M
  have hδM : δ ∈ M := IntermediateField.subset_adjoin _ _
    (by rw [Polynomial.mem_rootSet]; exact ⟨hmon.ne_zero, (hf_root δ).2 hδ⟩)
  have hform : ∀ z ∈ M, ∃ a b : F, z = algebraMap F Ω a + algebraMap F Ω b * δ := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin F (f.rootSet Ω) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
      exact hz
    clear hz
    induction hz' using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Polynomial.mem_rootSet, hf_root] at hx
      have hfx : (x - δ) * (x + δ) = 0 := by linear_combination hx.2 - hδ
      rcases mul_eq_zero.1 hfx with h | h
      · exact ⟨0, 1, by rw [map_zero, map_one]; linear_combination h⟩
      · exact ⟨0, -1, by rw [map_zero, map_neg, map_one]; linear_combination h⟩
    | algebraMap r => exact ⟨r, 0, by rw [map_zero]; ring⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by rw [map_add (f := _), map_add (f := _)]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      refine ⟨a * c - b * d * p, a * d + b * c, ?_⟩
      simp only [map_add (f := _), map_sub, map_mul, map_natCast]
      linear_combination (algebraMap F Ω b * algebraMap F Ω d) * hδ
  have hcond : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 →
      A.valuation (algebraMap M Ω (τ x) - algebraMap M Ω x) < 1 := by
    intro x hx
    rw [AlgEquiv.restrictNormal_commutes]
    obtain ⟨a, b, hab⟩ := hform (algebraMap M Ω x) x.2
    rw [hab] at hx ⊢
    have e : σ₀ (algebraMap F Ω a + algebraMap F Ω b * δ) - (algebraMap F Ω a + algebraMap F Ω b * δ)
        = (-2 : Ω) * (algebraMap F Ω b * δ) := by
      rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσ₀']; ring
    rw [e]
    have hb1 : A.valuation (algebraMap F Ω b * δ) < 1 := by
      by_cases hb : b = 0
      · rw [hb, map_zero, zero_mul, Valuation.map_zero]; exact zero_lt_one
      have hne1 := KL b hb
      have hne : A.valuation (algebraMap F Ω a) ≠ A.valuation (algebraMap F Ω b * δ) := by
        intro heq
        have hbd : algebraMap F Ω b * δ ≠ 0 := mul_ne_zero ((_root_.map_ne_zero _).2 hb) hδ0
        have ha : a ≠ 0 := by
          rintro rfl
          rw [map_zero, Valuation.map_zero] at heq
          exact hbd ((Valuation.zero_iff _).1 heq.symm)
        apply KL (b / a) (div_ne_zero hb ha)
        have haw : A.valuation (algebraMap F Ω a) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 ha)
        rw [map_div₀, div_mul_eq_mul_div, map_div₀, ← heq, div_self haw]
      rw [Valuation.map_add_of_distinct_val _ hne] at hx
      exact lt_of_le_of_ne (le_trans (le_max_right _ _) hx) hne1
    rw [map_mul]
    have h2 : A.valuation (-2 : Ω) ≤ 1 := by
      rw [Valuation.map_neg]
      have := valuation_natCast_le_one A 2
      simpa using this
    calc A.valuation (-2 : Ω) * A.valuation (algebraMap F Ω b * δ)
        ≤ 1 * A.valuation (algebraMap F Ω b * δ) := by gcongr
      _ < 1 := by rw [one_mul]; exact hb1
  obtain ⟨σ, hσ, hστ⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A M τ hcond
  refine ⟨σ, hσ, ?_⟩
  have h1 := hστ ⟨δ, hδM⟩
  rw [AlgEquiv.restrictNormal_commutes] at h1
  change σ δ = σ₀ δ at h1
  rw [h1, hσ₀']
  intro h
  have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact two_ne_zero h3
  · exact hδ0 h3

end GlobalTheory.SqrtNegRam
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_moves_square_root : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ discr F → ∀ (δ : Ω), δ ^ 2 = -(p : Ω) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ s ∈ Ine (F := F) A, s δ ≠ δ := by
  first | exact @GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia | exact GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia | (intros; apply GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia <;> assumption)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ExSplitCM

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem prime_eq_of_mem (u : HeightOneSpectrum (𝓞 F)) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : ((p : ℕ) : 𝓞 F) ∈ u.asIdeal) (h' : ((p' : ℕ) : 𝓞 F) ∈ u.asIdeal) : p = p' := by
  by_contra hne
  have hc : Nat.gcd p p' = 1 := (Nat.coprime_primes hp hp').2 hne
  have hm : (((Nat.gcd p p' : ℕ) : ℤ) : 𝓞 F) ∈ u.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab p p']
    push_cast
    exact u.asIdeal.add_mem (u.asIdeal.mul_mem_right _ h) (u.asIdeal.mul_mem_right _ h')
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem finite_primes_of_finite {B : Set (HeightOneSpectrum (𝓞 F))} (hB : B.Finite) :
    {p : ℕ | p.Prime ∧ ∃ u ∈ B, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}.Finite := by
  refine (hB.biUnion (t := fun u => {p : ℕ | p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun u _ => Set.Subsingleton.finite fun p hp p' hp' => prime_eq_of_mem u hp.1 hp'.1 hp.2 hp'.2).subset ?_
  rintro p ⟨hp, u, hu, h⟩
  exact Set.mem_biUnion hu ⟨hp, h⟩

theorem exists_mem_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show ((p : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at h2
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hne : M ≠ ⊥ := by
    intro h
    rw [h] at hle
    have h0 := hle (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_bot] at h0
    exact hp.ne_zero (by exact_mod_cast h0)
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.mem_span_singleton_self _)⟩

theorem mem_range_res_iff (K : IntermediateField F Ω) (σ : G F Ω) :
    σ ∈ (res F Ω ↥K).range ↔ ∀ x ∈ K, σ x = x := by
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => h _ x.2, rfl⟩

theorem fix_adjoin {δ : Ω} (hint : IsIntegral F δ) (s : G F Ω) (h : s δ = δ) :
    ∀ x ∈ IntermediateField.adjoin F {δ}, s x = x := by
  intro x hx
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
  have := (AlgHom.eqOn_adjoin_iff (φ := (s : Ω →ₐ[F] Ω)) (ψ := AlgHom.id F Ω)).2
    (by simpa [Set.EqOn] using h) hx
  simpa using this

theorem exists_qcm [IsTotallyReal F] [IsAlgClosure F Ω] (d : F) (δ : Ω) (hδ : δ ^ 2 = algebraMap F Ω d)
    (hd : ∀ φ : F →+* ℝ, φ d < 0) : ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ} := by
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Monic :=
      Polynomial.monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := Polynomial.natDegree_le_natDegree h1
    rwa [Polynomial.natDegree_X_pow_sub_C _] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let w : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h3 := hd ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  exact ⟨⟨K, inferInstance, IsCMField.ofCMExtension F K, hrk⟩, rfl⟩

end GlobalTheory.ExSplitCM

open GlobalTheory.ExSplitCM in
theorem GlobalTheory.RealGal.exists_infinite_qcm_split_ram : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : HeightOneSpectrum (𝓞 F) → Prop), (∀ᶠ u in Filter.cofinite, T u) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range}.Infinite := by
  intro F Ω _ _ _ _ _ _ T hT v A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  let Good : Set ℕ := {p | p.Prime ∧ IsSquare (-(p : ℚ_[q])) ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr F ∧
    ∀ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → T u}
  have hGood : Good.Infinite := by
    have hbad : ({2} ∪ {p : ℕ | p ∣ (discr F).natAbs} ∪
        {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) | ¬ T u}, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}).Finite := by
      refine ((Set.finite_singleton 2).union ?_).union (finite_primes_of_finite (Filter.eventually_cofinite.1 hT))
      exact (Nat.divisors (discr F).natAbs).finite_toSet.subset fun p hp =>
        Nat.mem_divisors.2 ⟨hp, Int.natAbs_ne_zero.2 (discr_ne_zero F)⟩
    refine ((GlobalTheory.T.infinite_primes_neg_square_padic q).diff hbad).mono ?_
    rintro p ⟨⟨hp, hs⟩, hn⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_and, not_exists] at hn
    refine ⟨hp, hs, hn.1.1, fun h => hn.1.2 (Int.natCast_dvd.1 h), fun u hu => ?_⟩
    by_contra hTu
    exact hn.2 hp u hTu hu
  have hQ : ∀ p ∈ Good, ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} := by
    intro p hp
    refine exists_qcm (-(p : F)) (δ p) (by simp [hδ p]) fun φ => ?_
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.1.pos
  have hmove : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      ∀ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal →
        IsPlaceOver A' u → ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range := by
    intro p hp Q hQK u A' hu hA' hle
    obtain ⟨s, hs, hne⟩ := GlobalTheory.T.inertia_moves_square_root F Ω p hp.1 hp.2.2.1 hp.2.2.2.1 (δ p) (hδ p) u A' hu hA'
    refine hne ((mem_range_res_iff Q.K s).1 (hle hs) (δ p) ?_)
    rw [hQK]
    exact IntermediateField.mem_adjoin_simple_self F (δ p)
  have hmem : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      Q ∈ {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range} := by
    intro p hp Q hQK
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.T.decomposition_fixes_square_root F Ω v A hA q hqv (-(p : ℤ)) (δ p) (by push_cast; exact hδ p)
        (by push_cast; exact hp.2.1) s hs
    · obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
      obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
      exact ⟨u, A', hp.2.2.2.2 u hu, hA', hmove p hp Q hQK u A' hu hA'⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : QCM F Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := F) A' ≤ (res F Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds F ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  exact ⟨u, fun hall => hmove p hp Q hQK u A' hu hA' (hall A' hA'), hu⟩
