module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnInParamKProd
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficients
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

private def LowZero {ι K : Type} [Field K] (a : ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m : ι →₀ ℕ, m.degree < a → MvPowerSeries.coeff m f = 0

private theorem lowZero_mul {ι K : Type} [Field K] {a b : ℕ} {f g : MvPowerSeries ι K}
    (hf : LowZero a f) (hg : LowZero b g) : LowZero (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hx', map_add (f := _)]
  by_cases h : x.1.degree < a
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem lowZero_one {ι K : Type} [Field K] : LowZero 0 (1 : MvPowerSeries ι K) :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

private theorem lowZero_pow {ι K : Type} [Field K] {f : MvPowerSeries ι K}
    (hf : LowZero 1 f) (e : ℕ) : LowZero e (f ^ e) := by
  induction e with
  | zero => simpa using lowZero_one
  | succ e ih => rw [pow_succ]; exact lowZero_mul ih hf

private theorem lowZero_prod {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (ha : ∀ i, LowZero 1 (a i)) (k : ι →₀ ℕ) (s : Finset ι) :
    LowZero (∑ i ∈ s, k i) (∏ i ∈ s, a i ^ k i) := by
  induction s using Finset.induction_on with
  | empty => simpa using lowZero_one
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lowZero_mul (lowZero_pow (ha i) _) ih

private theorem coeff_subst_low {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (hs : MvPowerSeries.HasSubst a) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (W : MvPowerSeries ι K) (d : ℕ) (hW : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0)
    (m : ι →₀ ℕ) (hm : m.degree ≤ d) : MvPowerSeries.coeff m (MvPowerSeries.subst a W) = 0 := by
  have ha1 : ∀ i, LowZero 1 (a i) := by
    intro i n hn
    have hn0 : n = 0 := by
      have : n.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff n).mp this
    rw [hn0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha i]
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  by_cases hk : k.degree ≤ d
  · rw [hW k hk, zero_smul]
  · have h := lowZero_prod a ha1 k k.support m (by
      have : k.degree = ∑ i ∈ k.support, k i := rfl
      omega)
    have e : (k.prod fun s e => a s ^ e) = ∏ i ∈ k.support, a i ^ k i := rfl
    rw [e, h, smul_zero]

theorem low_coeff_of_param (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1]
    [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p))
    (hUn : ∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0))
    (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ))
    (hS : ∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) (m : ι →₀ ℕ) (hm : m.degree ≤ d) :
    MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) *
      algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  have hs := Pf.en_Ec_hs p K1 (ι := ι)
  set c : (ι →₀ ℕ) → K1 := fun n => MvPowerSeries.coeff n (inParamK p K1 U) with hc

  have hmon : ∀ n, MvPowerSeries.subst (Pf.en_Ec p K1) (MvPowerSeries.monomial n (1 : K1)) =
      MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    intro n
    have h1 : inParamK p K1 (MvPowerSeries.map (algebraMap (K0 p) K1) (Un n)) =
        MvPowerSeries.monomial n (1 : K1) := by
      have h2 := Pf.th_inParamK_map p (K0 p) K1 (Un n)
      rw [h2, ← Pf.th_inParam_eq, (hUn n).1]
      ext k
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
      split_ifs <;> simp
    rw [← h1, Pf.en_Ec_inParamK]
  set W : MvPowerSeries ι K1 := inParamK p K1 U - ∑ n ∈ S, c n • MvPowerSeries.monomial n (1 : K1) with hWdef
  have hWlow : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0 := by
    intro k hk
    have hkS := hS k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hWdef, map_sub, map_sum]
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq S k]
    simp [hkS, hc]
  have hV : MvPowerSeries.subst (Pf.en_Ec p K1) W =
      U - ∑ n ∈ S, c n • MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hs, hWdef, map_sub, map_sum, MvPowerSeries.coe_substAlgHom hs,
      Pf.en_Ec_inParamK]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← MvPowerSeries.coe_substAlgHom hs, map_smul, MvPowerSeries.coe_substAlgHom hs, hmon n]
  have h0 := coeff_subst_low (Pf.en_Ec p K1) hs (Pf.en_Ec_zero p K1) W d hWlow m hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hV, map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hc, smul_eq_mul]

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficientsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowCoefficients_of_parameterCoefficients : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p)), (∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0)) → ∀ (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ)), (∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) → ∀ m : ι →₀ ℕ, m.degree ≤ d → MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) * algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  first | exact @GlobalTheory.TwU.low_coeff_of_param | exact GlobalTheory.TwU.low_coeff_of_param | (intros; apply GlobalTheory.TwU.low_coeff_of_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeries
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem inParam_eq_subst_log (p : ℕ) [Fact p.Prime] {ι : Type} (f : MvPowerSeries ι (K0 p)) :
    inParam p f = MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL p (K0 p)) f := by
  have h : Formalism.MainNotions.FormalGroupSystem.Pf.en_L p (K0 p) = logF p := by
    ext k; simp [Formalism.MainNotions.FormalGroupSystem.Pf.en_L]
  unfold inParam Formalism.MainNotions.FormalGroupSystem.Pf.en_aL
  rw [h]

theorem monomial_param_as_log_series : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ),
    ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  intro p _ ι _ n
  have hs := Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_hs p (K0 p) (ι := ι)
  have hl := Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_hs p (K0 p) (ι := ι)
  refine ⟨MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec p (K0 p)) (MvPowerSeries.monomial n (1 : K0 p)), ?_, ?_⟩
  · rw [inParam_eq_subst_log, MvPowerSeries.subst_comp_subst_apply hs hl]
    simp only [Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_Ec]
    rw [MvPowerSeries.subst_self]
    rfl
  · intro m hm
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le (Nat.cast_lt.mpr hm) ?_
    rw [MvPowerSeries.subst_monomial hs, map_one, one_mul, Finsupp.prod]
    refine le_trans ?_ (MvPowerSeries.le_order_prod _ _)
    have hd : n.degree = ∑ i ∈ n.support, n i := rfl
    rw [hd, Nat.cast_sum]
    exact Finset.sum_le_sum fun s _ =>
      MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_zero p (K0 p) s)

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeriesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ), ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  first | exact @GlobalTheory.TwU.monomial_param_as_log_series | exact GlobalTheory.TwU.monomial_param_as_log_series | (intros; apply GlobalTheory.TwU.monomial_param_as_log_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWitt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.LowGen

theorem le_order_subst' {σ τ K : Type} [Finite σ] [Field K] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    f.order ≤ (MvPowerSeries.subst a f).order := by
  refine le_trans ?_ (MvPowerSeries.le_order_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha i)
  calc f.order = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr

theorem applyD_eq_zero {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K)
    (h : ((P.totalDegree + 1 : ℕ) : ℕ∞) ≤ f.order) : applyD P f = 0 := by
  unfold applyD
  refine Finset.sum_eq_zero fun n hn => ?_
  have h1 : n.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree hn
  have h2 : MvPowerSeries.coeff n f = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    exact_mod_cast Nat.lt_succ_of_le h1
  rw [h2, mul_zero, zero_smul]

noncomputable def applyDL {σ τ : Type} (K : Type) [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) :
    MvPowerSeries σ K →ₗ[K] MvPolynomial τ K where
  toFun := applyD P
  map_add' f g := by
    simp only [applyD, map_add (f := _), mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [applyD, RingHom.id_apply, Finset.smul_sum, smul_smul, MvPowerSeries.coeff_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    ring

theorem applyD_map {σ τ K L : Type} [Field K] [Field L] (φ : K →+* L) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)]
  simp

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K j s) = 0 := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem map_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap (K0 p) K) (X.coordZA (K0 p) j s) = X.coordZA K j s := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem ThZA_map (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ)
    (f : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    X.ThZA K j (MvPowerSeries.map (algebraMap (K0 p) K) f) =
      MvPowerSeries.map (algebraMap (K0 p) K) (X.ThZA (K0 p) j f) := by
  unfold Sys.ThZA
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X _ j))]
  congr 1
  funext s
  exact (map_coordZA X K j s).symm

theorem p_ne_zero (K : Type) [Field K] [Algebra (K0 p) K] : (p : K) ≠ 0 := by
  have h : (p : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 := (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).mpr h
  have h3 := (map_ne_zero (algebraMap (K0 p) K)).mpr h2
  simpa using h3

theorem geC_of_mem {X : Sys p} (Y : Pend X) (g : ℝ) (y : Y.Kc) (hy : y ∈ Y.Oc) :
    Y.geC ((p : Y.Kc) ^ ⌈g⌉ * y) g := by
  intro a b hb hab
  have hp := p_ne_zero (p := p) Y.Kc
  have h1 : a ≤ ⌈g⌉ * b := by
    have : (a : ℝ) ≤ (⌈g⌉ : ℝ) * b := hab.trans (mul_le_mul_of_nonneg_right (Int.le_ceil g) (Nat.cast_nonneg b))
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h1)
  have : ((p : Y.Kc) ^ ⌈g⌉ * y) ^ b * (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ k * y ^ b := by
    rw [mul_pow, ← zpow_natCast ((p : Y.Kc) ^ ⌈g⌉), ← zpow_mul, mul_right_comm, ← zpow_add₀ hp, ← sub_eq_add_neg, hk,
      zpow_natCast]
  rw [this]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (natCast_mem Y.Oc p) _) (Y.Oc.pow_mem hy _)

theorem cofactor_lower_bound_of_place_bound_witt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ),
    MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  intro p _ X Y j v g _ hL U hU I m
  choose Un hUn using GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero p (X.EA j ⊕ X.EA j)
  set P := X.PIv j I v with hP
  set d := P.totalDegree with hd
  have hfin : {n : (X.EA j ⊕ X.EA j) →₀ ℕ | n.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  set S := hfin.toFinset with hS
  have hspan := GlobalTheory.T.lowCoefficients_of_parameterCoefficients p (X.EA j ⊕ X.EA j) Y.Kc Un hUn U d S (fun n hn => hfin.mem_toFinset.mpr hn)
  have hint : ∀ n, IntS p (inParam p (Un n)) := fun n =>
    ⟨MvPowerSeries.monomial n 1, by rw [(hUn n).1, MvPowerSeries.map_monomial, RingHom.map_one]⟩
  choose a ha using fun n => hL (Un n) (hint n) I m
  have hE : Y.PhAt j v = phAt X Y.be j v := rfl
  rw [hE]
  set E := expS p (-phAt X Y.be j v) with hEdef
  set φ := algebraMap (K0 p) Y.Kc with hφ
  set c : _ → Y.Kc := fun n => MvPowerSeries.coeff n (inParamK p Y.Kc U) with hc
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X Y.Kc j)
  set A := U - ∑ n ∈ S, c n • MvPowerSeries.map φ (Un n) with hA
  have hAo : ((d + 1 : ℕ) : ℕ∞) ≤ A.order := by
    apply MvPowerSeries.nat_le_order
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA, map_sub, hspan k (Nat.le_of_lt_succ hk), map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  have hz : applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * A)) = 0 := by
    apply applyD_eq_zero
    refine le_trans ?_ (le_order_subst' (constantCoeff_coordZA X Y.Kc j) _)
    exact hAo.trans (le_trans le_add_self MvPowerSeries.le_order_mul)
  have hU' : MvPowerSeries.map φ E * U =
      MvPowerSeries.map φ E * A + ∑ n ∈ S, c n • MvPowerSeries.map φ (E * Un n) := by
    rw [hA, mul_sub, Finset.mul_sum]
    simp only [mul_smul_comm, map_mul, sub_add_cancel]
  have hTh : ∀ f, applyD P (X.ThZA Y.Kc j f) =
      ((applyDL Y.Kc P) ∘ₗ (MvPowerSeries.substAlgHom (R := Y.Kc) hsub).toLinearMap) f := by
    intro f
    rw [Sys.ThZA, ← MvPowerSeries.coe_substAlgHom hsub]
    rfl
  have hval : AddMonoidAlgebra.coeff (applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * U))) m =
      (p : Y.Kc) ^ ⌈g⌉ * ∑ n ∈ S, c n * φ (algebraMap (WW p) (K0 p) (a n)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hU', hTh, map_add (f := _), ← hTh, hz, zero_add, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← hTh, hφ, ThZA_map, applyD_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, ha n, map_mul,
      map_zpow₀, map_natCast, smul_eq_mul]
    ring
  rw [hval]
  exact geC_of_mem Y g _ (Y.Oc.sum_mem fun n _ => Y.Oc.mul_mem (hU n) (Y.witt_mem_integers_Cp _))

end GlobalTheory.TwU.LowGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWittStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ), MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  first | exact @GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | exact GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | (intros; apply GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt <;> assumption)
end
