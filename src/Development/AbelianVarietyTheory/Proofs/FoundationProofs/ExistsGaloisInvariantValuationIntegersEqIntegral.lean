module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension
open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtensionStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectral_valuation_algebraic_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ), IsNonarchimedean f → f.IsNontrivial → CompleteSpace (WithAbs f) → ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧ ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  first | exact @GlobalTheory.exists_spectralValuation | exact GlobalTheory.exists_spectralValuation | (intros; apply GlobalTheory.exists_spectralValuation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_iff_isIntegral_of_complete_dvr :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω]
      [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) →
      ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  intro R Ω _ _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hinj
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  obtain ⟨f, hna, hnt, hball, hcomp⟩ := GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr R (FractionRing R)
  obtain ⟨v, -, hv⟩ := GlobalTheory.T.exists_spectral_valuation_algebraic_extension (FractionRing R) Ω f hna hnt hcomp
  refine ⟨v, fun x => ?_⟩
  rw [hv]
  simp only [hball]
  constructor
  · intro h
    have hl : minpoly (FractionRing R) x ∈ Polynomial.lifts (algebraMap R (FractionRing R)) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr h
    obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hmon, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (FractionRing R), hq]
    exact minpoly.aeval _ _
  · intro h i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvrStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr : ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  first | exact @GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | exact GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr | (intros; apply GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegral
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  obtain ⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
    have hmap : p.map (algebraMap R Ω) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    have hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω := by
      rintro _ ⟨k, rfl⟩
      rw [Polynomial.mem_rootSet']
      refine ⟨hmap, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp [hpx]
    have hfin := (Polynomial.rootSet_finite p Ω).subset hsub
    have hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x) := fun hi =>
      Set.infinite_range_of_injective hi hfin
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x)) := strictAnti_nat_of_succ_lt hs
    have := hanti hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hmono : StrictMono (fun n : ℕ => v ((g ^ n) x)) := strictMono_nat_of_lt_succ hs
    have := hmono hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegralStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) → ∀ (g : Ω ≃ₐ[R] Ω) (x : Ω), v (g x) = v x := by
  first | exact @GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | exact GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | (intros; apply GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_valuation_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) ∧
      (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact GlobalTheory.T.unramified_integers_adic_complete p
  haveI := h.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, ?_, ?_⟩
  · exact (Valuation.pos_iff v).2 hp0
  · have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegralStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∃ v : Valuation Ω ℝ≥0,
        (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧
        (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := h.alg
  have hvaluation :=
    GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  obtain ⟨v, hv⟩ := hvaluation
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, (Valuation.pos_iff v).2 hp0, ?_⟩
  have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
    have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    simpa [GlobalTheory.K5.IsInt] using this)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
  have hint : GlobalTheory.K5.IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
  exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
    ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
end
