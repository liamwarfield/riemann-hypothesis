module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHom
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.HomCount

theorem card_ker_eq (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (Y : Submodule R X) :
    Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
      = Nat.card {g : (X ⧸ Y) →ₗ[R] M // LinearMap.ker g = ⊥} := by
  refine Nat.card_congr
    { toFun := fun f => ⟨Y.liftQ f.1 f.2.ge, Submodule.ker_liftQ_eq_bot _ _ _ f.2.le⟩
      invFun := fun g => ⟨g.1 ∘ₗ Y.mkQ, by
        rw [LinearMap.ker_comp, g.2]
        exact Y.ker_mkQ⟩
      left_inv := fun f => Subtype.ext (Y.liftQ_mkQ _ _)
      right_inv := fun g => Subtype.ext ?_ }
  apply Submodule.linearMap_qext
  exact Y.liftQ_mkQ _ _

theorem finite_hom (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] : Finite (X →ₗ[R] M) :=
  Finite.of_injective (fun f : X →ₗ[R] M => (f : X → M)) DFunLike.coe_injective

theorem card_hom_eq_sum (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] [Fintype (Submodule R X)] :
    Nat.card (X →ₗ[R] M)
      = ∑ Y : Submodule R X, Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y} := by
  haveI := finite_hom R X M
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun f : X →ₗ[R] M => LinearMap.ker f)).symm

theorem card_inj_eq (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N]
    (h : ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X],
      Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) (n : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card X = n →
      Nat.card {f : X →ₗ[R] M // LinearMap.ker f = ⊥}
        = Nat.card {f : X →ₗ[R] N // LinearMap.ker f = ⊥} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ _ hX
    haveI : Finite (Submodule R X) :=
      Finite.of_injective (fun Y : Submodule R X => (Y : Set X)) SetLike.coe_injective
    letI : Fintype (Submodule R X) := Fintype.ofFinite _
    have h1 := h X
    rw [card_hom_eq_sum, card_hom_eq_sum,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X))] at h1
    have h2 : ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
        = ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] N // LinearMap.ker f = Y} := by
      refine Finset.sum_congr rfl fun Y hY => ?_
      have hY' : Y ≠ ⊥ := Finset.ne_of_mem_erase hY
      rw [card_ker_eq R X M, card_ker_eq R X N]
      haveI : Finite (X ⧸ Y) := Finite.of_surjective _ Y.mkQ_surjective
      refine ih (Nat.card (X ⧸ Y)) ?_ (X ⧸ Y) rfl
      rw [← hX]
      refine lt_of_le_of_ne (Nat.card_le_card_of_surjective _ Y.mkQ_surjective) fun he => hY' ?_
      have hb : Function.Bijective Y.mkQ :=
        (Function.Surjective.bijective_of_nat_card_le Y.mkQ_surjective he.ge)
      rw [← Y.ker_mkQ]
      exact LinearMap.ker_eq_bot.2 hb.1
    omega

theorem nonempty_equiv_of_card_hom :
    ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ h
  haveI := finite_hom R M M
  haveI := finite_hom R N N
  have h1 := card_inj_eq R M N h _ M rfl
  have h2 := card_inj_eq R M N h _ N rfl
  haveI : Nonempty {f : M →ₗ[R] M // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  haveI : Nonempty {f : N →ₗ[R] N // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  have p1 : 0 < Nat.card {f : M →ₗ[R] N // LinearMap.ker f = ⊥} := h1 ▸ Nat.card_pos
  have p2 : 0 < Nat.card {f : N →ₗ[R] M // LinearMap.ker f = ⊥} := h2 ▸ Nat.card_pos
  obtain ⟨⟨f, hf⟩⟩ := (Nat.card_pos_iff.1 p1).1
  obtain ⟨⟨g, hg⟩⟩ := (Nat.card_pos_iff.1 p2).1
  rw [LinearMap.ker_eq_bot] at hf hg
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ hg)
  exact ⟨LinearEquiv.ofBijective f hb⟩

end GlobalTheory.HomCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHomStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (exact GlobalTheory.HomCount.nonempty_equiv_of_card_hom) | (intros; apply GlobalTheory.HomCount.nonempty_equiv_of_card_hom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.PowCancel

def linMapPiEquiv (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    (X →ₗ[R] (Fin l → M)) ≃ (Fin l → (X →ₗ[R] M)) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext x i; rfl
  right_inv g := by funext i; ext x; rfl

theorem card_linMap_pow (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] M) ^ l := by
  rw [Nat.card_congr (linMapPiEquiv R X M l), Nat.card_fun, Nat.card_fin]

theorem cancel_pow : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l →
    Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ l hl ⟨e⟩
  refine GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq R M N ?_
  intro X _ _ _
  have h1 : Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] (Fin l → N)) :=
    Nat.card_congr
      { toFun := fun f => e.toLinearMap.comp f
        invFun := fun g => e.symm.toLinearMap.comp g
        left_inv := fun f => by ext x; simp
        right_inv := fun g => by ext x; simp }
  rw [card_linMap_pow, card_linMap_pow] at h1
  exact Nat.pow_left_injective hl.ne' h1

end GlobalTheory.PowCancel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFiniteStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l → Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.PowCancel.cancel_pow) | (exact GlobalTheory.PowCancel.cancel_pow) | (intros; apply GlobalTheory.PowCancel.cancel_pow  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

open Set Filter Topology

theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem fourier_phi1_eq_factorial_mul_zpow : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ),
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  intro k hk hke w hw x
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hwx : w - (x : ℂ) ≠ 0 := by
    intro h
    apply hw
    have := congrArg Complex.im h
    simpa using this
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [Nat.add_sub_cancel]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rcases hw.lt_or_gt with hneg | hpos
  · set r : ℂ := 2 * Real.pi * Complex.I * (w - x) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (-v) * x) * Complex.I) • phi1 (m + 1) w (-v)) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_neg hneg, SignType.coe_neg,
        SignType.coe_one, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos (by linarith), if_pos hv, abs_neg, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg (by linarith), if_neg hv, mul_zero]
    rw [← integral_neg_eq_self, e, integral_indicator measurableSet_Ioi,
      integral_pow_mul_cexp_neg m hr, hrdef, mul_pow, zpow_neg, zpow_natCast]
    field_simp
  · set r : ℂ := -(2 * Real.pi * Complex.I * (w - x)) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • phi1 (m + 1) w v) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_pos hpos,
        SignType.coe_one, one_mul, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos hv, if_pos hv, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [e, integral_indicator measurableSet_Ioi, integral_pow_mul_cexp_neg m hr, hrdef,
      hke.neg_pow, mul_pow, zpow_neg, zpow_natCast]
    field_simp

end GlobalTheory.LipschitzTR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEqStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ), 𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  first | exact @GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | exact GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | (intros; apply GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleMemOfMem
open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

end GlobalTheory.Div.KerFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpan
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N,
    (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  intro C _ w S _ _ a N F ha hF x hx hc
  have hle : ∀ s, filSpace F s ≤ clearDen F s := fun s => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨diffGen a s, diffGen_ne_zero a ha s, single_mem_of_mem a F hF.stable s y hy⟩
  choose b hb hbx using fun s => hle s (hc s)
  have hB : (∏ s, b s) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hb s
  refine hF.saturated x hx (∏ s, b s) hB ?_
  have key : (∏ s, b s) • x = ∑ s, (∏ t ∈ Finset.univ.erase s, b t) •
      (Pi.single s (b s • x s) : S → Fin N → C) := by
    funext s' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s']
    · simp only [smul_pi_apply, Pi.single_eq_same, smul_vec_apply]
      rw [← mul_assoc, ← Subring.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s')]
    · intro s _ e
      simp [smul_pi_apply, Pi.single_apply, Ne.symm e]
    · simp
  rw [key]
  exact sum_mem fun s _ => F.smul_mem _ (hbx s)

end GlobalTheory.Div.KerFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpanStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  first | exact @GlobalTheory.Div.KerFil.mem_of_components | exact GlobalTheory.Div.KerFil.mem_of_components | (intros; apply GlobalTheory.Div.KerFil.mem_of_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section CupDelta

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem sum_alt_filter_lt_le (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel

theorem delta_cup_eq : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 → ∀ u,
    delta (cup Φ c) u = cup Φ (delta c) u + ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card •
      delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) := by
  intro ι _ E _ Φ c hΦ hc u

  have sL : ∀ {i j : ι}, i < j → cubeSign u i = cubeSign (u.filter (· ≤ j)) i := by
    intro i j hij
    have : (u.filter (· ≤ j)).filter (· < i) = u.filter (· < i) := by
      ext x; simp only [Finset.mem_filter]; grind
    unfold cubeSign; rw [this]
  have sR : ∀ {i j : ι}, j < i → cubeSign u i =
      (-1 : ℤ) ^ (u.filter (· < j)).card * cubeSign (u.filter (j ≤ ·)) i := by
    intro i j hji
    have hd : Disjoint (u.filter (· < j)) ((u.filter (j ≤ ·)).filter (· < i)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact absurd h1.2 (not_lt.2 h2.1.2)
    have : u.filter (· < i) = u.filter (· < j) ∪ (u.filter (j ≤ ·)).filter (· < i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]; grind
    unfold cubeSign; rw [← pow_add, ← Finset.card_union_of_disjoint hd, this]

  have hL : delta (cup Φ c) u = ∑ j ∈ u, ∑ i ∈ u.erase j,
      cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) := by
    simp only [delta, cup, Finset.smul_sum]
    exact Finset.sum_comm' (fun i j => by simp only [Finset.mem_erase]; tauto)

  have key : ∀ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
      ∑ i ∈ u.erase j,
        cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) := by
    intro j hj
    have eL : (u.erase j).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eG : (u.erase j).filter (fun x => ¬ x < j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eLeL : (u.filter (· ≤ j)).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eLeJ : (u.filter (· ≤ j)).filter (fun x => ¬ x < j) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eGeG : (u.filter (j ≤ ·)).filter (j < ·) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eGeJ : (u.filter (j ≤ ·)).filter (fun x => ¬ j < x) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eLeE : (u.filter (· ≤ j)).erase j = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eGeE : (u.filter (j ≤ ·)).erase j = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind

    rw [← Finset.sum_filter_add_sum_filter_not (u.erase j) (· < j), eL, eG]

    have h1 : Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) +
        (-1 : ℤ) ^ (u.filter (· < j)).card • Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [delta, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (· ≤ j)) (· < j), eLeL, eLeJ,
        Finset.sum_singleton, eLeE]
      congr 2
      unfold cubeSign; rw [eLeL]

    have h2 : delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), cubeSign (u.filter (j ≤ ·)) i •
          Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·)) := by
      simp only [delta]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (j ≤ ·)) (j < ·), eGeG, eGeJ,
        Finset.sum_singleton, eGeE, cubeSign_eq_one_of_forall_le (by simp), one_smul]
    rw [h1, h2, smul_add, Finset.smul_sum]
    have hA : ∑ i ∈ u.filter (· < j), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := (Finset.mem_filter.1 hi).2
      rw [sL hij, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (j ≤ ·)) (by simp [hij])]
    have hB : ∑ i ∈ u.filter (j < ·), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), (-1 : ℤ) ^ (u.filter (· < j)).card •
          cubeSign (u.filter (j ≤ ·)) i • Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j < i := (Finset.mem_filter.1 hi).2
      rw [sR hji, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (· ≤ j)) (by simp [hji]), mul_smul]
    rw [hA, hB]
    simp only [smul_add]
    abel

  have tele := sum_alt_filter_lt_le (fun s => Φ (c s) (u \ s)) u
  simp only [Finset.sdiff_self, hΦ, Finset.sdiff_empty, hc, map_zero, Pi.zero_apply, smul_zero,
    sub_zero] at tele
  have hT : ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
      Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) = 0 := by
    rw [← tele]
    refine Finset.sum_congr rfl fun j _ => ?_
    have a1 : u \ u.filter (· < j) = u.filter (j ≤ ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    have a2 : u \ u.filter (· ≤ j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    rw [a1, a2]
  rw [hL]
  show _ = ∑ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) + _
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib, hT, add_zero]

end CupDelta

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc.Translate

theorem exists_X_sub_C_mem_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k]
    (Q : Ideal k[X]) [hQ : Q.IsPrime] :
    ∀ (n : ℕ) (g : k[X]), g ≠ 0 → g.natDegree = n → g ∈ Q → ∃ r : k, X - C r ∈ Q := by
  intro n
  induction n with
  | zero =>
    intro g hg hdeg hgQ
    exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hgQ hg
    have h0 : g.coeff 0 ≠ 0 := fun h => hg (by rw [h, map_zero])
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgQ (isUnit_C.2 (IsUnit.mk0 _ h0)))
  | succ n ih =>
    intro g hg hdeg hgQ
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg, hdeg]; exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := g) (a := r)).2 hr
    rw [← hdiv] at hgQ hg
    rcases hQ.mem_or_mem hgQ with h | h
    · exact ⟨r, h⟩
    · refine ih _ (right_ne_zero_of_mul hg) ?_ h
      have := natDegree_divByMonic g (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [this, hdeg]; omega

theorem exists_X_sub_C_mem (T : Type) [CommRing T] [IsLocalRing T] [IsAlgClosed (ResidueField T)]
    (P : Ideal T[X]) [hPp : P.IsPrime] (hP : P.comap (C : T →+* T[X]) = maximalIdeal T)
    (hne : P ≠ (maximalIdeal T).map (C : T →+* T[X])) : ∃ c : T, X - C c ∈ P := by
  set π : T[X] →+* (ResidueField T)[X] := mapRingHom (residue T) with hπ
  have hsurj : Function.Surjective π := map_surjective _ residue_surjective
  have hker : RingHom.ker π = (maximalIdeal T).map (C : T →+* T[X]) := by
    rw [hπ, ker_mapRingHom, ker_residue]
  have hle : RingHom.ker π ≤ P := by
    rw [hker, Ideal.map_le_iff_le_comap, hP]
  haveI hQ : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hle
  have hPQ : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hle
  have hQbot : P.map π ≠ ⊥ := by
    intro h
    apply hne
    rw [← hker, ← hPQ, h, RingHom.ker_eq_comap_bot]
  obtain ⟨g, hgQ, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQbot
  obtain ⟨r, hr⟩ := exists_X_sub_C_mem_of_isAlgClosed _ _ _ g hg rfl hgQ
  obtain ⟨c, rfl⟩ := residue_surjective r
  refine ⟨c, ?_⟩
  rw [← hPQ, Ideal.mem_comap]
  simpa [hπ] using hr

end GlobalTheory.LocAcyc.Translate

namespace GlobalTheory.LocAcyc.Translate

theorem keyClosedPts_of_keyOrigin : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  intro hKO
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith at hKO
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne q hq hqu
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP' q hq hqu

end GlobalTheory.LocAcyc.Translate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibreStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  first | (exact @GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (exact GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (intros; apply GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegreeStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  first | exact @GlobalTheory.DI.alt_and_phi_vanish_above_degree | exact GlobalTheory.DI.alt_and_phi_vanish_above_degree | (intros; apply GlobalTheory.DI.alt_and_phi_vanish_above_degree <;> assumption)
end
end
