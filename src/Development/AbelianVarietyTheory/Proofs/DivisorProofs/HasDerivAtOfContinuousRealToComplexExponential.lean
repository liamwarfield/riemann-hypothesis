module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousOfMapAdd
namespace GlobalTheory.DerivativeOfAdditiveContinuous

theorem hasDerivAt_of_continuous_of_map_add (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c := ∫ t in (0 : ℝ)..η, χ t with hcdef
  have hc0 : c ≠ 0 := by
    have hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1) := by
      rw [hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
      simp
    have hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hη0.le] at ht
      have h1 : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have h2 := hball t h1
      rw [dist_eq_norm, h0] at h2
      exact h2.le
    intro hzero
    rw [hsplit] at hzero
    have h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η := by
      rw [eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη0]
    rw [h3, sub_zero, abs_of_pos hη0] at hbound
    linarith
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF
  have hFd : ∀ x, HasDerivAt F (χ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hrep : ∀ x, χ x * c = F (x + η) - F x := by
    intro x
    have h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c := by
      simp only [hadd]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    rw [← h1, h2, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hdiff : ∀ x, DifferentiableAt ℝ χ x := by
    intro x
    have hχ : χ = fun y => (F (y + η) - F y) / c := by
      funext y
      rw [← hrep y, mul_div_cancel_right₀ _ hc0]
    rw [hχ]
    exact (((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c
  have hd0 : HasDerivAt χ (deriv χ 0) (s - s) := by
    rw [sub_self]
    exact (hdiff 0).hasDerivAt
  have hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s := hd0.comp_sub_const s s
  have hmul := hcomp.const_mul (χ s)
  have hfun : (fun y => χ s * χ (y - s)) = χ := by
    funext y
    rw [← hadd]
    congr 1
    ring
  rw [hfun] at hmul
  rw [mul_comm]
  exact hmul

end GlobalTheory.DerivativeOfAdditiveContinuous
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential
open scoped ContDiff

namespace GlobalTheory

theorem hasDerivAt_of_continuous_additive_to_mul (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first
  | exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | (apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponentialStatement
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first | exact @GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | exact GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | (intros; apply GlobalTheory.hasDerivAt_of_continuous_additive_to_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
namespace GlobalTheory

theorem exists_injective_rows_leadingMinors_not_mem (R : Type) [CommRing R] (p : Ideal R) :
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) R), T.det ∉ p →
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ (k : ℕ) (hk : k ≤ n),
      (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)).det ∉ p := by
  intro n
  induction n with
  | zero =>
    intro T hT
    refine ⟨id, Function.injective_id, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    have h1 : T.det = 1 := Matrix.det_isEmpty
    rw [Matrix.det_isEmpty]
    rwa [h1] at hT
  | succ n ih =>
    intro T hT
    have hsum := T.det_succ_column (Fin.last n)
    obtain ⟨i, hi⟩ : ∃ i : Fin (n+1), (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * T i (Fin.last n) *
        (T.submatrix i.succAbove (Fin.last n).succAbove).det ∉ p := by
      by_contra h
      push_neg at h
      exact hT (hsum ▸ p.sum_mem fun i _ => h i)
    have hM : (T.submatrix i.succAbove Fin.castSucc).det ∉ p := by
      intro hm
      apply hi
      rw [Fin.succAbove_last]
      exact p.mul_mem_left _ hm
    obtain ⟨g, hg, hmin⟩ := ih _ hM
    set f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (g j))
    have hf : Function.Injective f := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab.symm (Fin.succAbove_ne i _)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab (Fin.succAbove_ne i _)
        | cast b =>
          simp only [f, Fin.lastCases_castSucc] at hab
          rw [hg (Fin.succAbove_right_injective hab)]
    refine ⟨f, hf, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have hmat : (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          Matrix.of fun a b : Fin k => (T.submatrix i.succAbove Fin.castSucc)
            (g (Fin.castLE hk' a)) (Fin.castLE hk' b) := by
        ext a b
        have e1 : (Fin.castLE hk a : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' a) := Fin.ext rfl
        have e2 : (Fin.castLE hk b : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' b) := Fin.ext rfl
        rw [Matrix.of_apply, Matrix.of_apply, e1, e2]
        simp only [f, Fin.lastCases_castSucc, Matrix.submatrix_apply]
      rw [hmat]
      exact hmin k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
      have hmat : (Matrix.of fun a b : Fin (n+1) => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          T.submatrix σ id := by
        ext a b
        have e1 : Fin.castLE hk a = a := Fin.ext rfl
        have e2 : Fin.castLE hk b = b := Fin.ext rfl
        simp [σ, e1, e2]
      rw [hmat, Matrix.det_permute]
      intro hm
      apply hT
      have hs : T.det = ((Equiv.Perm.sign σ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R) * T.det) := by
        rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      rw [hs]
      exact p.mul_mem_left _ hm

theorem exists_rowPerm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p →
    ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n),
      ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  intro R _ n T p _ hT
  obtain ⟨f, hf, h⟩ := exists_injective_rows_leadingMinors_not_mem R p n T hT
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun k hk => h k hk⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMemStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ) (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p → ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n), ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  first | exact @GlobalTheory.exists_rowPerm_leadingMinors_not_mem | exact GlobalTheory.exists_rowPerm_leadingMinors_not_mem | (intros; apply GlobalTheory.exists_rowPerm_leadingMinors_not_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0
open Polynomial

namespace GlobalTheory

theorem isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _

theorem linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef
  have hq0 : aeval T q v = 0 := by
    have h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v
        = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k) := by
      intro k hk
      rw [← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X,
        aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]
  have hq : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval_of_forall_isUnit_sub T h q hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [hq0, map_zero]))
  have h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j) := by
    rw [hqdef, Polynomial.eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hki
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩)
        (by simp), mul_zero]
    · intro h; exact absurd hi h
  rw [hq, eval_zero] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm

theorem dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidance
open scoped Matrix

namespace GlobalTheory

theorem exists_conj_skew_det_unit_of_avoidance :
  ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by
  intro F R _ _ _ _ c hcc hcF e H ρ hρ hcρ n J₀ ε hJ hdet D C x₀ hx₀
  obtain ⟨e', he'⟩ : ∃ a : R, a = ((ε : ℤ) : R) := ⟨_, rfl⟩
  rw [← he'] at hJ
  have hee : e' * e' = 1 := by
    rw [he', ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : c e' = e' := by rw [he']; exact map_intCast c _
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  have hc2 : c (⅟2 : R) = ⅟2 := by
    have h1 : c (⅟2 : R) * 2 = 1 := by
      have := congrArg c (invOf_mul_self (2 : R))
      rwa [map_mul, map_ofNat, map_one] at this
    calc c (⅟2 : R) = c (⅟2) * (2 * ⅟2) := by rw [h2, mul_one]
      _ = ⅟2 := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨r, hr'⟩ : ∃ a : R, a = ↑hρ.unit⁻¹ := ⟨_, rfl⟩
  have hr : ρ * r = 1 := by rw [hr']; exact hρ.mul_val_inv
  have hcr : c r = -r := by
    have h1 : c r * (-ρ) = 1 := by rw [← hcρ, ← map_mul, mul_comm, hr, map_one]
    linear_combination (-r) * h1 + (-c r) * hr
  have hKdet : IsUnit (J₀ᵀ).det := by rw [Matrix.det_transpose]; exact hdet
  have hLK : J₀ᵀ⁻¹ * J₀ᵀ = 1 := Matrix.nonsing_inv_mul _ hKdet
  have hLtJ : (J₀ᵀ⁻¹)ᵀ * J₀ = 1 := by
    have : J₀ * (J₀ᵀ⁻¹)ᵀ = 1 := by
      have := congrArg Matrix.transpose hLK
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact mul_eq_one_comm.mp this
  have hJLc : J₀ * (J₀ᵀ⁻¹).map c = e' • 1 := by
    have h1 : (J₀ᵀ⁻¹).map c * (e' • J₀) = 1 := by
      have := congrArg c.mapMatrix hLK
      rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map, hJ] at this
      exact this
    have h3 : (e' • J₀) * (J₀ᵀ⁻¹).map c = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h3
    calc J₀ * (J₀ᵀ⁻¹).map c = (e' * e') • (J₀ * (J₀ᵀ⁻¹).map c) := by rw [hee, one_smul]
      _ = e' • (e' • (J₀ * (J₀ᵀ⁻¹).map c)) := by rw [mul_smul]
      _ = e' • 1 := by rw [h3]
  obtain ⟨M₀, hM₀⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = J₀ᵀ * x₀ := ⟨_, rfl⟩
  obtain ⟨v, hv'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (⅟2 : R) • (M₀ - Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (r * ⅟2) • (M₀ + Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  have hv : ∀ i j, v j i + e' * c (v i j) = 0 := by
    intro i j
    simp only [hv', Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_sub, hc2, hce, hcc]
    linear_combination (-(⅟2 : R) * M₀ j i) * hee
  have hw : ∀ i j, w j i + e' * c (w i j) = 0 := by
    intro i j
    simp only [hw', Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_add, hc2, hce, hcc, hcr]
    linear_combination (-(r * ⅟2) * M₀ j i) * hee
  have hsum : v + ρ • w = M₀ := by
    ext i j
    simp only [hv', hw', Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
      smul_eq_mul]
    linear_combination ((⅟2 : R) * (M₀ i j + e' * c (M₀ j i))) * hr + M₀ i j * h2
  have hcond : ∀ s, c s = s →
      (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ + J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = 0 := by
    intro s hs
    have e1 : (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ = (v + s • w)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, hLtJ, Matrix.mul_one]
    have e2 : J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = e' • (v + s • w).map c := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, hJLc, Matrix.smul_mul, Matrix.one_mul]
    rw [e1, e2]
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, map_add, map_mul, hs, Matrix.zero_apply]
    linear_combination hv i j + s * hw i j
  obtain ⟨ψ, hψ⟩ : ∃ p : Polynomial R, p = ((D + C * J₀ᵀ⁻¹ * v).map Polynomial.C +
      (Polynomial.X : Polynomial R) • (C * J₀ᵀ⁻¹ * w).map Polynomial.C).det := ⟨_, rfl⟩
  have hev : ∀ s, ψ.eval s = (D + C * (J₀ᵀ⁻¹ * (v + s • w))).det := by
    intro s
    have hre : D + C * (J₀ᵀ⁻¹ * (v + s • w)) = (D + C * J₀ᵀ⁻¹ * v) + s • (C * J₀ᵀ⁻¹ * w) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_assoc]
    rw [hre, hψ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
  have hρev : ψ.eval ρ = (D + C * x₀).det := by
    rw [hev, hsum, hM₀, ← Matrix.mul_assoc J₀ᵀ⁻¹, hLK, Matrix.one_mul]
  have hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0 := by
    intro Ω _ φ hφ h0
    have h1 := congrArg (Polynomial.eval (φ ρ)) h0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_zero, hρev] at h1
    have hu := hx₀.map φ
    rw [map_add (f := _), map_mul, map_sub, map_one, hφ, one_mul, sub_self, add_zero, h1] at hu
    exact not_isUnit_zero hu
  obtain ⟨t, ht⟩ := H ψ hne
  refine ⟨J₀ᵀ⁻¹ * (v + algebraMap F R t • w), hcond _ (hcF t), ?_⟩
  rwa [hev] at ht

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulOneSubLeChoose
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem choose_mul_one_sub_le_choose (N M D : ℕ) (x : ℝ) (hx : 0 ≤ x) (hDM : D ≤ M) (hMN : M ≤ N)
    (h : (N : ℝ) - M ≤ x * ((N : ℝ) - D + 1)) :
    ∀ k ≤ D, ((N.choose k : ℕ) : ℝ) * (1 - k * x) ≤ ((M.choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hkD : k ≤ D := by omega
    have ih' := ih hkD
    have hkM : k ≤ M := by omega
    have hkN : k ≤ N := by omega
    have eN : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hkN]
      exact_mod_cast h
    have eM : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq M k
      rw [← Nat.cast_sub hkM]
      exact_mod_cast h
    have hk1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hA : (0 : ℝ) ≤ ((N.choose k : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity

    have hbr : (0 : ℝ) ≤ x * ((N : ℝ) - k) + x * k * ((N : ℝ) - M) - ((N : ℝ) - M) := by
      have h1 : x * ((N : ℝ) - D + 1) ≤ x * ((N : ℝ) - k) := by
        apply mul_le_mul_of_nonneg_left _ hx
        linarith
      have h2 : 0 ≤ x * k * ((N : ℝ) - M) := by
        have : (0 : ℝ) ≤ (N : ℝ) - M := by linarith
        positivity
      linarith
    have hstep : ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x)
        ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h3 : ((N.choose k : ℕ) : ℝ) * (1 - k * x) * ((M : ℝ) - k)
          ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h4 := mul_nonneg hA hbr
      nlinarith [h3, h4]
    have goal' : ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
        ≤ ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      rw [eM]
      calc ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
          = ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1) * x) := by ring
        _ = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x) := by rw [eN]
        _ ≤ _ := hstep
    push_cast
    exact le_of_mul_le_mul_right goal' hpos

theorem share_bound_of_jet_count :
    ∀ (D T a : ℕ) (ρ δ d : ℝ), 2 ≤ D → D + 1 ≤ T → 0 ≤ ρ → ρ ≤ 1 / 2 → T + D + 3 ≤ a → (a : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) → 0 ≤ δ → 0 ≤ d → d ≤ (((a + D).choose D : ℕ) : ℝ) * δ → (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by
  intro D T a ρ δ d hD hDT hρ0 hρ hTa ha hδ hd0 hd
  have hT1 : 1 ≤ T := by omega
  have hT : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  have hTr : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]
    simp
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hTa' : (T : ℝ) + D + 3 ≤ a := by exact_mod_cast hTa
  have hxnn : 0 ≤ 4 * (D : ℝ) / T + ρ := by positivity

  have key := choose_mul_one_sub_le_choose (a + D) (T - 1) D (4 * (D : ℝ) / T + ρ) hxnn
    (by omega) (by omega) (by
      push_cast
      rw [hTr]
      have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
      have hamul : (a : ℝ) * (1 - ρ) ≤ (T : ℝ) + D + 3 := (le_div_iff₀ h1ρ).mp ha
      have h4 : 4 * (D : ℝ) ≤ 4 * (D : ℝ) / T * ((a : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]
        have : (0 : ℝ) ≤ 4 * D := by positivity
        nlinarith
      nlinarith [h4, hamul, hρ0, hD2]) D le_rfl
  have hc : 1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ) ≤ 1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ) := by
    have e : (D : ℝ) * (4 * (D : ℝ) / T + ρ) = 4 * ((D : ℝ) ^ 2 / T) + D * ρ := by ring
    have h1 : 0 ≤ (D : ℝ) ^ 2 / T := by positivity
    have h2 : 0 ≤ (D : ℝ) * ρ := by positivity
    rw [e]
    linarith
  have hB : (0 : ℝ) ≤ (((a + D).choose D : ℕ) : ℝ) * δ := by positivity
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by positivity
  rcases le_or_gt (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) 0 with h | h
  · have : (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hd0
    linarith
  · calc (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d
        ≤ (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hd h.le
      _ ≤ (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_right hc hB
      _ = ((((a + D).choose D : ℕ) : ℝ) * (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ))) * δ := by ring
      _ ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right key hδ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
open scoped TensorProduct
open Function

namespace GlobalTheory
open TensorProduct MulOpposite

variable (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ]

noncomputable def endBaseChangeMap :
    S ⊗[A] Module.End A Λ →ₗ[S] Module.End S (S ⊗[A] Λ) :=
  (LinearMap.baseChangeHom A S Λ Λ).liftBaseChange S

lemma endBaseChangeMap_tmul (s : S) (f : Module.End A Λ) :
    endBaseChangeMap A S Λ (s ⊗ₜ f) = s • f.baseChange S := by
  simp [endBaseChangeMap]

lemma endBaseChangeMap_bijective [Module.Free A Λ] [Module.Finite A Λ] :
    Bijective (endBaseChangeMap A S Λ) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A Λ
  let b := Module.Free.chooseBasis A Λ
  let bS := Algebra.TensorProduct.basis S b
  let e₁ : S ⊗[A] Module.End A Λ ≃ₗ[S] S ⊗[A] Matrix ι ι A :=
    (LinearMap.toMatrix b b).baseChange A S _ _
  let e₂ := (matrixEquivTensor ι A S).symm
  let e₃ := LinearMap.toMatrix bS bS
  have h : ∀ x, e₃ (endBaseChangeMap A S Λ x) = e₂ (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s f =>
      simp [e₁, e₂, e₃, bS, endBaseChangeMap_tmul, matrixEquivTensor_apply_symm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have : (endBaseChangeMap A S Λ : _ → _) = e₃.symm ∘ e₂ ∘ e₁ := by
    funext x; simp [← h x]
  rw [this]
  exact e₃.symm.bijective.comp (e₂.bijective.comp e₁.bijective)

noncomputable def opBaseChange : S ⊗[A] Λᵐᵒᵖ ≃ₗ[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  ((opLinearEquiv A (M := Λ)).symm.baseChange A S _ _).trans (opLinearEquiv S)

noncomputable def envBaseChange :
    S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ) ≃ₗ[S] (S ⊗[A] Λ) ⊗[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  (AlgebraTensorModule.distribBaseChange A S Λ Λᵐᵒᵖ).trans
    (TensorProduct.congr (LinearEquiv.refl S _) (opBaseChange A S Λ))

lemma mulLeftRight_envBaseChange (x : S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ)) :
    AlgHom.mulLeftRight S (S ⊗[A] Λ) (envBaseChange A S Λ x) =
      endBaseChangeMap A S Λ ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add (f := _), hy, hz]
    | tmul a b =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add (f := _), hz, hw]
      | tmul t y =>
        simp [envBaseChange, opBaseChange, endBaseChangeMap_tmul,
          AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          smul_tmul', mul_comm, mul_left_comm]

theorem isAzumaya_baseChange [IsAzumaya A Λ] [Module.Free A Λ] :
    IsAzumaya S (S ⊗[A] Λ) := by
  classical
  haveI : Module.Finite A Λ := inferInstance
  refine { toProjective := inferInstance, toFinite := inferInstance,
           toFaithfulSMul := ?_, bij := ?_ }
  · rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨fun _ => Subsingleton.elim _ _⟩
    · haveI : Nontrivial A := (algebraMap A S).domain_nontrivial
      haveI : Nontrivial Λ := by
        by_contra hΛ
        rw [not_nontrivial_iff_subsingleton] at hΛ
        have : (0 : A) = 1 :=
          FaithfulSMul.eq_of_smul_eq_smul (α := Λ) fun _ => Subsingleton.elim _ _
        exact zero_ne_one this
      let b := Module.Free.chooseBasis A Λ
      let bS := Algebra.TensorProduct.basis S b
      obtain ⟨i⟩ := b.index_nonempty
      refine ⟨fun {s₁ s₂} h => ?_⟩
      have := congrArg (fun x => bS.repr x i) (h (bS i))
      simpa using this
  · have hφ : Bijective ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) := by
      let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight A Λ).toLinearMap IsAzumaya.bij
      have : (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S = (e.lTensor S : _ →ₗ[A] _) := rfl
      rw [this]; exact (e.lTensor S).bijective
    have hc : (AlgHom.mulLeftRight S (S ⊗[A] Λ) : _ → _) =
        (endBaseChangeMap A S Λ ∘ (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) ∘
          (envBaseChange A S Λ).symm := by
      funext y
      simp [← mulLeftRight_envBaseChange]
    rw [hc]
    exact ((endBaseChangeMap_bijective A S Λ).comp hφ).comp (envBaseChange A S Λ).symm.bijective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChangeStatement
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_base_change : ∀ (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ], IsAzumaya S (S ⊗[A] Λ) := by
  first | (exact @GlobalTheory.isAzumaya_baseChange) | (exact GlobalTheory.isAzumaya_baseChange) | (intros; apply GlobalTheory.isAzumaya_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerMore
namespace GlobalTheory.InductiveNormBound

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w^2 - 1‖ := by
  have e : w^2 - 1 = (w - 1) * ((w - 1) + 2) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖ := by
    have h3 := norm_sub_le ((w - 1) + 2) (w - 1)
    have h4 : (w - 1) + 2 - (w - 1) = (2:ℂ) := by ring
    rw [h4] at h3
    have : ‖(2:ℂ)‖ = 2 := by simp
    linarith
  have h0 := norm_nonneg (w - 1)
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ k : ℕ, (3/2 : ℝ)^k * ‖z - 1‖ ≤ ‖z^(2^k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step (z^(2^k)) (hz _)
      have e : (z^(2^k))^2 = z^(2^(k+1)) := by rw [← pow_mul, ← pow_succ]
      rw [e] at hs
      have hp : (3/2:ℝ)^(k+1) = (3/2)^k * (3/2) := pow_succ _ _
      rw [hp]
      nlinarith [ih, hs]
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key k
  have h2 := hz (2^k)
  have h3 : 1 < (3/2:ℝ)^k * ‖z - 1‖ := by
    rw [div_lt_iff₀ hpos] at hk; linarith
  linarith

end GlobalTheory.InductiveNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
noncomputable section

namespace GlobalTheory.CocycleChar

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_character_cocycle_trivial_near_zero : ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  first | exact @GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | exact GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | (intros; apply GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
open TensorProduct

namespace GlobalTheory

namespace PicPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]

theorem exists_one_tmul (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i)
    (z : R i ⊗[(j : ι) → R j] M) : ∃ y : M, (1 : R i) ⊗ₜ y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, hA]
    simp
  | add a b ha hb =>
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    exact ⟨ya + yb, by rw [TensorProduct.tmul_add]⟩

theorem single_smul_eq_zero (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i) (y : M)
    (h : (1 : R i) ⊗ₜ[(j : ι) → R j] y = 0) : (Pi.single i 1 : (j : ι) → R j) • y = 0 := by
  let φ : R i →ₗ[(j : ι) → R j] M →ₗ[(j : ι) → R j] M :=
    LinearMap.mk₂ _ (fun r y => (Pi.single i r : (j : ι) → R j) • y)
      (fun r₁ r₂ y => by simp only [Pi.single_add, add_smul])
      (fun s r y => by
        have hs : (Pi.single i (s • r) : (j : ι) → R j) = s * Pi.single i r := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [Algebra.smul_def, hA]
          · simp [hj]
        simp only [hs, mul_smul])
      (fun r y₁ y₂ => smul_add _ _ _)
      (fun s r y => smul_comm _ _ _)
  have := congrArg (TensorProduct.lift φ) h
  simpa [φ] using this

variable [Fintype ι]

theorem eq_one_of_forall (M : CommRing.Pic ((j : ι) → R j))
    (h : ∀ i, CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M = 1) : M = 1 := by
  letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  have hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i := fun i => rfl
  have e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i := by
    intro i
    have hi := h i
    rw [← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply,
      CommRing.Pic.mk_eq_one_iff] at hi
    exact hi.some
  choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)
  let m₀ : M := ∑ i, (Pi.single i 1 : (j : ι) → R j) • m i
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀) := by
    intro x
    refine ⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩
    have key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x =
        (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i := by
      intro i
      set r := e i ((1 : R i) ⊗ₜ x) with hr
      have h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x =
          (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i) := by
        apply (e i).injective
        rw [← TensorProduct.smul_tmul]
        have h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r := by
          rw [Algebra.smul_def, hA i]; simp
        rw [h0]
        have h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      have h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0 := by
        rw [TensorProduct.tmul_sub, h1, sub_self]
      have h3 := single_smul_eq_zero i M (hA i) _ h2
      rw [smul_sub, sub_eq_zero, smul_smul] at h3
      rw [h3, ← Pi.single_mul, one_mul]
    rw [LinearMap.toSpanSingleton_apply, Finset.smul_sum]
    have hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) •
        (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x := by
      intro i
      rw [key i, smul_smul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]
    have h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1 := by
      simpa using Finset.univ_sum_single (1 : (j : ι) → R j)
    rw [h1, one_smul]
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact CommRing.Pic.mk_eq_self.symm.trans
    (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)

end PicPi

theorem pic_pi_isOfFinOrder : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  intro ι _ R _ hR M
  classical
  haveI := Fintype.ofFinite ι
  have hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M) :=
    Finset.prod_pos fun i _ => (hR i _).orderOf_pos
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩
  apply PicPi.eq_one_of_forall
  intro i
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

end GlobalTheory
end
