module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeMemHeightOneSpectrum
namespace GlobalTheory.PrimeInHeightOneSpectrum

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))
    have hpr : Nat.Prime n.minFac := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hmul : ((n.minFac : R) * (m : R)) ∈ P := by
      rw [← Nat.cast_mul, ← hm]; exact hmem
    rcases hP.mem_or_mem hmul with h | h
    · exact ⟨_, hpr, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hlt : m < n := by
        rw [hm]
        have := hpr.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      exact ih m hlt hm0 h

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
end

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.FewPrimes

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
  apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption

end GlobalTheory.Mem.FewPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
open Finset ArithmeticFunction

namespace GlobalTheory

theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N, vonMangoldt_mul_zeta]
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]
    rfl

theorem sum_vonMangoldt_div_nat_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ∧
      ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hF := log_factorial_eq_sum_vonMangoldt_mul_div N
  have hfp : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hup : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log hfp (by exact_mod_cast N.factorial_le_pow)
  have hlo : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp, Real.log_div (by positivity) hfp.ne', Real.log_pow] at h2
    linarith
  have h1 : Real.log (N.factorial : ℝ) ≤ N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) := by
    rw [hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    calc Λ n * ((N / n : ℕ) : ℝ) ≤ Λ n * ((N : ℝ) / n) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = N * (Λ n / n) := by ring
  have h2 : N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤
      Real.log (N.factorial : ℝ) + ∑ n ∈ Ioc 0 N, Λ n := by
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have h := Nat.lt_div_mul_add (a := N) hn0
      have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast h
      linarith
    calc (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
      _ ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hlt vonMangoldt_nonneg
      _ = _ := by ring
  have h3 : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have h := Chebyshev.psi_le_const_mul_self hN'.le
    rwa [Chebyshev.psi, Nat.floor_natCast] at h
  constructor
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith

theorem mertens_first_vonMangoldt :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 + 4, by positivity, fun y hy => ?_⟩
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hN' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN
  have hI : Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  obtain ⟨h1, h2⟩ := sum_vonMangoldt_div_nat_bounds _ hN
  have h5 : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h6 : Real.log y ≤ Real.log 4 + Real.log ⌊y⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    have := Nat.lt_floor_add_one y
    linarith
  rw [hI, abs_le]
  constructor <;> linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
open IsLocalRing

namespace GlobalTheory

private lemma mem_colon_span_range_iff {B : Type*} [CommRing B] {P : Ideal B} {ι : Type*}
    (g : ι → B) (r : B) :
    r ∈ P.colon (Ideal.span (Set.range g) : Set B) ↔ ∀ i, r * g i ∈ P := by
  rw [Ideal.colon_span, Submodule.mem_colon]
  simp only [Set.forall_mem_range, smul_eq_mul]

theorem _root_.GlobalTheory.ideal_map_colon_eq_of_flat : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  intro A R _ _ _ φ hφ I J
  obtain ⟨n, a, hJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨m, b, hI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  replace hJ : Ideal.span (Set.range a) = J := hJ
  replace hI : Ideal.span (Set.range b) = I := hI
  subst hJ hI
  rw [Ideal.map_span φ (Set.range a), ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_colon_span_range_iff]
    rw [mem_colon_span_range_iff] at hr
    intro i
    simpa [map_mul] using Ideal.mem_map_of_mem φ (hr i)
  · intro s hs
    rw [mem_colon_span_range_iff] at hs
    have hmapI : (Ideal.span (Set.range b)).map φ = Ideal.span (Set.range (φ ∘ b)) := by
      rw [Ideal.map_span, ← Set.range_comp]
    choose c hc using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hmapI ▸ hs i)
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hφ
    let f : (Fin n → A) →ₗ[A] A × (Fin n × Fin m → A) :=
      LinearMap.prod (Fintype.linearCombination A a)
        (LinearMap.pi fun p => -(b p.2) • LinearMap.proj p.1)
    let x : A × (Fin n × Fin m → A) →ₗ[A] R :=
      LinearMap.coprod (LinearMap.toSpanSingleton A R s)
        (Fintype.linearCombination A fun p => c p.1 p.2)
    have hxf : x ∘ₗ f = 0 := by
      refine LinearMap.ext fun v => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp [f, x, Algebra.smul_def, Fintype.sum_prod_type, Fintype.linearCombination_apply,
        LinearMap.pi_apply, map_sum, Finset.sum_mul]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∑ j, algebraMap A R (b j) * algebraMap A R (v i) * c i j
          = algebraMap A R (v i) * ∑ j, c i j * (φ ∘ b) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
        ring
      rw [e, hc i]
      simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
      ring
    obtain ⟨k, g, y, hxy, hgf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
    have hdec : ∀ w : A × (Fin n × Fin m → A), g w = w.1 • g (1, 0) +
        ∑ p, w.2 p • g (0, fun q => if p = q then 1 else 0) := by
      intro w
      have hw : w = w.1 • ((1 : A), (0 : Fin n × Fin m → A)) + ((0 : A), w.2) := by
        ext <;> simp
      conv_lhs => rw [hw]
      rw [map_add (f := _), map_smul]
      congr 1
      exact LinearMap.pi_apply_eq_sum_univ (g ∘ₗ LinearMap.inr A A (Fin n × Fin m → A)) w.2
    have key : ∀ q, g (1, 0) q ∈
        (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set A) := by
      intro q
      rw [mem_colon_span_range_iff]
      intro i
      set w := f (fun j => if i = j then 1 else 0) with hw
      have hw1 : w.1 = a i := by simp [hw, f, Fintype.linearCombination_apply]
      have hw2 : ∀ p, w.2 p ∈ Ideal.span (Set.range b) := by
        intro p
        simp only [hw, f, LinearMap.prod_apply, Function.prod, LinearMap.pi_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.subset_span ⟨p.2, rfl⟩))
      have h0 := DFunLike.congr_fun (hdec w) q
      rw [show g w = 0 from LinearMap.congr_fun hgf _] at h0
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply] at h0
      have h1 : g (1, 0) q * a i = -∑ p, w.2 p * g (0, fun q => if p = q then 1 else 0) q := by
        rw [← hw1]
        linear_combination -h0
      rw [h1]
      exact neg_mem (Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hw2 p))
    have hs' : s = x (1, 0) := by simp [x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs', hxy, LinearMap.comp_apply, ← Finsupp.univ_sum_single (g (1, 0)), map_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (key q))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquiv
open IsLocalRing

namespace GlobalTheory.AdicQuot

open AdicCompletion

variable {A : Type} [CommRing A] (J q : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  rfl

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (Ideal.Quotient.mk q)) ^ n).comap (Ideal.Quotient.mk q) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* (A ⧸ q) ⧸ (J.map (Ideal.Quotient.mk q)) ^ n :=
  (Ideal.quotientMap _ (Ideal.Quotient.mk q) (pow_le_comap J q n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (Ideal.Quotient.mk q (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev J q n) = lev J q m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap J q m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
  AdicCompletion.liftRingHom _ (lev J q) (fun hle ↦ lev_compat J q hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by
  simp [psi]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem ker_psi [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Submodule.mkQ q) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]

theorem psi_surjective [IsNoetherianRing A] : Function.Surjective (psi J q) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J (A ⧸ q) := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (Submodule.mkQ_surjective q) (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff J q s n (t n)).mp ?_
  rw [hx]; rfl

end GlobalTheory.AdicQuot

theorem GlobalTheory.adicCompletion_quotient_ringEquiv :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A),
      Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+*
        AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  intro A _ _ J q
  exact ⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquivStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A), Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  first | exact @GlobalTheory.adicCompletion_quotient_ringEquiv | exact GlobalTheory.adicCompletion_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_quotient_ringEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
open NumberField

namespace GlobalTheory
namespace ProjModClasses

variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]

noncomputable def rep (c : ClassGroup R) : Ideal R :=
  ((ClassGroup.mk0_surjective (R := R) c).choose : Ideal R)

theorem rep_mem (c : ClassGroup R) : rep c ∈ nonZeroDivisors (Ideal R) :=
  (ClassGroup.mk0_surjective (R := R) c).choose.2

theorem mk0_rep (c : ClassGroup R) : ClassGroup.mk0 ⟨rep c, rep_mem c⟩ = c :=
  (ClassGroup.mk0_surjective (R := R) c).choose_spec

instance ideal_projective (I : Ideal R) : Module.Projective R I := by
  have : Module.FinitePresentation R I := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem map_mulLeft_eq (x : R) (I : Ideal R) :
    Submodule.map (LinearMap.mulLeft R x) I = Ideal.span {x} * I := by
  ext z
  rw [Ideal.mem_span_singleton_mul, Submodule.mem_map]
  simp [LinearMap.mulLeft_apply]

noncomputable def mulEquiv {x : R} (hx : x ≠ 0) (I : Ideal R) :
    I ≃ₗ[R] (Ideal.span {x} * I : Ideal R) :=
  (Submodule.equivMapOfInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) I).trans
    (LinearEquiv.ofEq _ _ (map_mulLeft_eq x I))

theorem nonempty_equiv_of_mk0_eq {I J : nonZeroDivisors (Ideal R)}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) : Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  exact ⟨(mulEquiv hx I).trans ((LinearEquiv.ofEq _ _ hxy).trans (mulEquiv hy J).symm)⟩

abbrev Model {r : ℕ} (c : Fin r → ClassGroup R) : Type := ∀ j, (rep (c j) : Ideal R)

noncomputable def consLin {r : ℕ} (d : ClassGroup R) (c : Fin r → ClassGroup R) :
    (↥(rep d) × Model c) ≃ₗ[R] Model (Fin.cons d c : Fin (r + 1) → ClassGroup R) :=
  { Fin.consEquiv (fun j => ↥(rep ((Fin.cons d c : Fin (r + 1) → ClassGroup R) j))) with
    map_add' := fun a b => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    map_smul' := fun s a => by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl }

theorem exists_equiv_model : ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X], Module.finrank R X = r →
    ∃ c : Fin r → ClassGroup R, Nonempty (X ≃ₗ[R] Model c) := by
  intro r
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hX
      rw [not_subsingleton_iff_nontrivial] at hX
      have := (Module.finrank_pos_iff (R := R) (M := X)).2 hX
      omega
    exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have hX : Nontrivial X := (Module.finrank_pos_iff (R := R) (M := X)).1 (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    set I : Ideal R := LinearMap.range f with hIdef
    have hI : I ≠ ⊥ := fun h0 => hf (by
      have : f x ∈ I := LinearMap.mem_range_self f x
      rw [h0] at this
      simpa using this)
    let g : X →ₗ[R] I := f.rangeRestrict
    have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict f
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
    let K := LinearMap.ker g
    have hex : Function.Exact K.subtype g := LinearMap.exact_subtype_ker_map g
    let e := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).1
    have he := ((hex.splitSurjectiveEquiv Subtype.val_injective) ⟨s, hs⟩).2
    haveI : Module.Projective R K := by
      refine Module.Projective.of_split K.subtype (LinearMap.fst R K I ∘ₗ e.toLinearMap) ?_
      ext y
      have h1 : (K.subtype y) = e.symm (y, 0) := by
        rw [he.1]; rfl
      show ((e (K.subtype y)).1 : X) = (y : X)
      rw [h1]
      simp

    have hrk := LinearMap.rank_range_add_rank_ker g
    rw [LinearMap.range_eq_top.2 hg, rank_top] at hrk
    have hIne : Nontrivial I := Submodule.nontrivial_iff_ne_bot.2 hI
    have hI1 : Module.finrank R I = 1 := by
      have a := (Module.finrank_pos_iff (R := R) (M := I)).2 hIne
      have b : Module.finrank R I ≤ 1 := (Submodule.finrank_le I).trans (by simp)
      omega
    have hK : Module.finrank R K = r := by
      have := congrArg Cardinal.toNat hrk
      rw [Cardinal.toNat_add (Module.rank_lt_aleph0 R I) (Module.rank_lt_aleph0 R K)] at this
      change Module.finrank R I + Module.finrank R K = Module.finrank R X at this
      omega
    obtain ⟨c, ⟨eK⟩⟩ := ih K hK
    have hmem : I ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hI
    obtain ⟨eI⟩ := nonempty_equiv_of_mk0_eq (I := ⟨I, hmem⟩)
      (J := ⟨rep (ClassGroup.mk0 ⟨I, hmem⟩), rep_mem _⟩) (mk0_rep _).symm
    exact ⟨Fin.cons (ClassGroup.mk0 ⟨I, hmem⟩) c,
      ⟨e.trans ((LinearEquiv.prodComm R K I).trans ((eI.prodCongr eK).trans (consLin _ c)))⟩⟩

end ProjModClasses

open ProjModClasses in
theorem exists_fin_reps_projective_finrank_le :
    ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  intro E _ _ q
  let T := Σ r : Fin (q + 1), (Fin r → ClassGroup (𝓞 E))
  let g : T → ModuleCat.{0} (𝓞 E) := fun t => ModuleCat.of (𝓞 E) (Model t.2)
  let P : T → Prop := fun t => Module.Finite (𝓞 E) (g t) ∧ Module.Projective (𝓞 E) (g t) ∧
    Module.finrank (𝓞 E) (g t) ≤ q
  let S := {t : T // P t}
  haveI : Finite S := inferInstance
  let eS := Finite.equivFin S
  refine ⟨Nat.card S, fun k => g (eS.symm k).1, fun k => (eS.symm k).2, ?_⟩
  intro X _ _ _ _ hq
  obtain ⟨c, ⟨eX⟩⟩ := exists_equiv_model (R := 𝓞 E) (Module.finrank (𝓞 E) X) X rfl
  let t : T := ⟨⟨Module.finrank (𝓞 E) X, Nat.lt_succ_of_le hq⟩, c⟩
  have ht : P t := by
    refine ⟨Module.Finite.equiv eX, Module.Projective.of_equiv eX, ?_⟩
    change Module.finrank (𝓞 E) (Model c) ≤ q
    rw [← eX.finrank_eq]
    exact hq
  refine ⟨eS ⟨t, ht⟩, ?_⟩
  show Nonempty (X ≃ₗ[𝓞 E] (g (eS.symm (eS ⟨t, ht⟩)).1))
  rw [Equiv.symm_apply_apply]
  exact ⟨eX⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberFieldStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  first | exact @GlobalTheory.exists_fin_reps_projective_finrank_le | exact GlobalTheory.exists_fin_reps_projective_finrank_le | (intros; apply GlobalTheory.exists_fin_reps_projective_finrank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RelDimFibCrit

end GlobalTheory.RelDimFibCrit

namespace GlobalTheory.RelDimFibCrit

open AlgebraicGeometry CategoryTheory Limits in
private lemma specMap_residueFieldMap_conj_eq_ofHom_map {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (p : PrimeSpectrum S) :
    (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
  haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
    rw [reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]
    erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]
    erw [Scheme.Spec.residue_residueFieldIso_hom]
    erw [Scheme.Hom.germ_stalkMap_assoc]
    erw [Spec.germ_stalkMapIso_hom_assoc]
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    erw [Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
  ext1
  apply Ideal.ResidueField.ringHom_ext
  exact congr_arg CommRingCat.Hom.hom key

open AlgebraicGeometry CategoryTheory Limits in
private lemma residueFieldCongr_hom_hom_comp {Y : Scheme.{0}} {a b : Y} {Z : CommRingCat.{0}}
    (h : a = b) (h' : b = a) (g : Y.residueField a ⟶ Z) :
    (Y.residueFieldCongr h).hom ≫ (Y.residueFieldCongr h').hom ≫ g = g := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_le_of_ringEquiv {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L ≤ Algebra.trdeg K' L' :=
  ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_eq_of_ringEquiv {K L K' L' : Type} [Field K] [CommRing L] [Field K']
    [CommRing L'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  refine le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)
  ext a
  have := congr($h (e₁.symm a))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this
  simp [this]


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by
  obtain ⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p := ⟨p, rfl⟩
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))
  set φ := f.appLE U V e
  haveI := hU.isOpenImmersion_fromSpec
  haveI := hV.isOpenImmersion_fromSpec
  have h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p) :=
    congr($(hU.SpecMap_appLE_fromSpec f hV e) p)
  set q : Spec Γ(Y, U) := (Spec.map φ) p
  let eL := (asIso (hV.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv
  let eK := (Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫
    Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv
  have hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso _ q).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) =
      f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso _ p).hom := by
    erw [← specMap_residueFieldMap_conj_eq_ofHom_map]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q),
      ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _),
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]
    exact (congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)
  refine @trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_
  ext a
  exact congr((CommRingCat.Hom.hom $hsq) a)

end GlobalTheory.RelDimFibCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBound
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem schur_scalar_bound (u w C₀ c₀ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    u ^ 2 + w ^ 2 ≤ (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) *
      ((1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2) := by
  set α := C₀ / c₀ with hα
  have hα0 : 0 ≤ α := div_nonneg hC hc.le
  set p := w - α * u with hp
  have e : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 = u ^ 2 + c₀ * p ^ 2 := by
    rw [hp, hα]; field_simp; ring
  have hw : w = p + α * u := by rw [hp]; ring
  have h1 : u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := by
    rw [hw]
    nlinarith [mul_nonneg hα0 (sq_nonneg (p - u)), mul_nonneg hα0 (sq_nonneg u),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg u), mul_nonneg hα0 (sq_nonneg p),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg p)]
  set M := max 1 (1 / c₀) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMc : 1 ≤ M * c₀ := by
    have : 1 / c₀ ≤ M := le_max_right _ _
    rw [div_le_iff₀ hc] at this; linarith
  have h2 : u ^ 2 + p ^ 2 ≤ M * (u ^ 2 + c₀ * p ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hM1 (sq_nonneg u),
      mul_le_mul_of_nonneg_right hMc (sq_nonneg p)]
  rw [e]
  calc u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := h1
    _ ≤ (1 + α) ^ 2 * (M * (u ^ 2 + c₀ * p ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem dot_sq_le (n : ℕ) (x v : Fin n → ℝ) : (x ⬝ᵥ v) ^ 2 ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  simpa [dotProduct, sq] using this

theorem dot_self_nonneg' (n : ℕ) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem schur_block_lower_bound : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  intro k l a bt b d C₀ c₀ b₀ hC hc hb _ _ _ ha hbb hd hbt z
  set x : Fin k → ℝ := z ∘ Sum.inl with hx
  set y : Fin l → ℝ := z ∘ Sum.inr with hy
  set L := (1 + C₀ + C₀ ^ 2 / c₀) / b₀ with hL
  have hsum : ∀ (f g : Fin k ⊕ Fin l → ℝ), f ⬝ᵥ g = (f ∘ Sum.inl) ⬝ᵥ (g ∘ Sum.inl) + (f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr) := by
    intro f g; simp [dotProduct, Fintype.sum_sum_type]
  have htr : y ⬝ᵥ b.transpose.mulVec x = x ⬝ᵥ b.mulVec y := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hexp : z ⬝ᵥ (Matrix.fromBlocks (a + L • bt) b b.transpose d).mulVec z
      = x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hsum, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← hx, ← hy, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_add,
      dotProduct_smul, htr, smul_eq_mul]
    ring
  have hzz : z ⬝ᵥ z = x ⬝ᵥ x + y ⬝ᵥ y := hsum z z
  rw [hexp, hzz]
  set U := x ⬝ᵥ x
  set W := y ⬝ᵥ y
  have hU : 0 ≤ U := dot_self_nonneg' k x
  have hW : 0 ≤ W := dot_self_nonneg' l y
  set u := Real.sqrt U
  set w := Real.sqrt W
  have hu : u ^ 2 = U := Real.sq_sqrt hU
  have hw : w ^ 2 = W := Real.sq_sqrt hW
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _

  have hQ : |x ⬝ᵥ b.mulVec y| ≤ C₀ * u * w := by
    have h1 := dot_sq_le k x (b.mulVec y)
    have h2 := hbb y
    have h3 : (x ⬝ᵥ b.mulVec y) ^ 2 ≤ (C₀ * u * w) ^ 2 := by
      calc (x ⬝ᵥ b.mulVec y) ^ 2 ≤ U * (b.mulVec y ⬝ᵥ b.mulVec y) := h1
        _ ≤ U * (C₀ ^ 2 * W) := mul_le_mul_of_nonneg_left h2 hU
        _ = (C₀ * u * w) ^ 2 := by rw [← hu, ← hw]; ring
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2 |> fun h => abs_le.mpr ⟨(abs_le_of_sq_le_sq' h3 (by positivity)).1, h⟩
  have hT : -(C₀ * U) ≤ x ⬝ᵥ a.mulVec x := by
    have := ha x; exact (abs_le.mp this).1
  have hB : (1 + C₀ + C₀ ^ 2 / c₀) * U ≤ L * (x ⬝ᵥ bt.mulVec x) := by
    have h := hbt x
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    calc (1 + C₀ + C₀ ^ 2 / c₀) * U = L * (b₀ * U) := by rw [hL]; field_simp
      _ ≤ L * (x ⬝ᵥ bt.mulVec x) := mul_le_mul_of_nonneg_left h hL0
  have hD := hd y
  have hQ' := (abs_le.mp hQ).1
  have key := schur_scalar_bound u w C₀ c₀ hC hc
  have hK : 0 < (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) := by
    have : 0 < 1 + C₀ / c₀ := by have := div_nonneg hC hc.le; linarith
    exact mul_pos (pow_pos this 2) (lt_of_lt_of_le one_pos (le_max_left _ _))
  rw [inv_mul_le_iff₀ hK]
  have hS : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 ≤
      x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hu, hw]; nlinarith
  calc U + W = u ^ 2 + w ^ 2 := by rw [hu, hw]
    _ ≤ _ := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hS hK.le

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBoundStatement
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_complement_block_quadratic_lower_bound : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  first | exact @GlobalTheory.schur_block_lower_bound | exact GlobalTheory.schur_block_lower_bound | (intros; apply GlobalTheory.schur_block_lower_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt
namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw2 : z ^ (2 ^ (k + 1)) = w ^ 2 := by rw [hw, ← pow_mul, pow_succ]
    have hlt : ‖w - 1‖ < 1 / 2 := h _
    have hplus : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : w + 1 = (2 : ℂ) + (w - 1) := by ring
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have := norm_sub_norm_le (2 : ℂ) (-(w - 1))
      rw [e]
      have h3 : ‖(2 : ℂ) - -(w - 1)‖ = ‖(2 : ℂ) + (w - 1)‖ := by rw [sub_neg_eq_add]
      rw [norm_neg, h2, h3] at this
      linarith
    have fac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hw2, fac, norm_mul, pow_succ]
    have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * (3 / 2) := by gcongr
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := by gcongr

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsFormBaseChange
namespace GlobalTheory

theorem _root_.GlobalTheory.ksForm_baseChange :
    ∀ {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']
      (ι : LL →+* LL'), (∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) →
      ∀ {n : ℕ} (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n → LL')),
      (∀ x, x ∈ WK ↔ (fun k => ι (x k)) ∈ WK') →
      (∀ x' ∈ WK', ∃ x ∈ WK, x' = fun k => ι (x k)) →
      (∃ (m : ℕ) (b : Fin m → (Fin n → LL)), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧
        Submodule.span LL (Set.range b) = ⊤) →
      ∃ (m : ℕ) (b : Fin m → (Fin n → LL')), (∀ i, b i ∈ WK') ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK' ∧ LinearIndependent LL' b ∧
        Submodule.span LL' (Set.range b) = ⊤ := by
  intro LL LL' Ks _ _ _ _ _ ι hι n WK WK' hmem hsurj ⟨m, b, hbW, hKs, hspanK, hLL, hspanLL⟩
  let Φ : (Fin n → LL) →ₗ[Ks] (Fin n → LL') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by ext k; simp
      map_smul' := fun c x => by ext k; simp [Algebra.smul_def, hι] }
  have hker : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => funext fun k => ?_
    have hk : ι (x k) = 0 := congrFun hx k
    simpa using hk
  have hmn : m = n := by
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hLL (by rw [hspanLL]))
    simp at h
    omega
  subst hmn
  have hLL' : LinearIndependent LL' (Φ ∘ b) := by
    have hu : IsUnit (Matrix.of b) := Matrix.linearIndependent_rows_iff_isUnit.1 hLL
    exact Matrix.linearIndependent_rows_iff_isUnit.2 (hu.map ι.mapMatrix)
  refine ⟨m, Φ ∘ b, fun i => (hmem _).1 (hbW i), hKs.map' Φ hker, ?_, hLL', ?_⟩
  · rw [Set.range_comp, Submodule.span_image, hspanK]
    ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := hsurj x' hx'
      exact ⟨x, hx, rfl⟩
  · exact hLL'.span_eq_top_of_card_eq_finrank' (by simp)

end GlobalTheory
end
