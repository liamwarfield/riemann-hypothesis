module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeGtDvdEval
namespace GlobalTheory.PrimeDivisorOfPolynomialValue

open Polynomial

theorem exists_eval_mul_ne (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by

  have hdeg : 0 < (f.comp (C a * X)).natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]
    exact hf
  have hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0 := fun b h => by
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
    ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)
  refine ⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩
  · rw [Multiset.mem_toFinset, mem_roots (hne c)]
    simp [e]
  · rw [Multiset.mem_toFinset, mem_roots (hne (-c))]
    simp [e]

theorem exists_prime_gt_dvd_eval :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by
  intro f hf n

  have of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
    intro x hx
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩
  by_cases h0 : f.eval 0 = 0
  · exact of_root 0 h0
  have hfac : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  obtain ⟨k, hk1, hk2⟩ := exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)
  by_cases hx : f.eval (f.eval 0 * n.factorial * k) = 0
  · exact of_root _ hx

  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f
  have hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q) := by
    linear_combination hq
  have ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1 := fun h => hk1 (by rw [hft, h, mul_one])
  have ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1 := fun h => hk2 (by rw [hft, h, mul_neg_one])
  have hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.1 h with h | h
    · exact ht1 (by simpa using h)
    · exact ht2 (by simpa using h)
  have hp := Nat.minFac_prime hnat
  have hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q) :=
    Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
  refine ⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩

  by_contra hle
  rw [not_lt] at hle
  have h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _
  have h4 := dvd_sub hpt h3
  rw [add_sub_cancel_right] at h4
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))

end GlobalTheory.PrimeDivisorOfPolynomialValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEval
open scoped TensorProduct Polynomial

namespace GlobalTheory


open Polynomial in
theorem exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEvalStatement
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval : ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first | exact @GlobalTheory.exists_prime_gt_dvd_eval | exact GlobalTheory.exists_prime_gt_dvd_eval | (intros; apply GlobalTheory.exists_prime_gt_dvd_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSq
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial

theorem int_bezout_derivative_of_separable (f : ℤ[X])
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ A B : ℤ[X], ∃ N : ℤ, N ≠ 0 ∧ A * f + B * derivative f = C N := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c1, hc1_mem, hc1⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) a
  obtain ⟨c2, hc2_mem, hc2⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b
  refine ⟨c2 • A, c1 • B, c1 * c2, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.ne_zero hc1_mem) (nonZeroDivisors.ne_zero hc2_mem)
  · apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    have e1 : A.map (Int.castRingHom ℚ) = (c1 : ℚ) • a := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc1]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    have e2 : B.map (Int.castRingHom ℚ) = (c2 : ℚ) • b := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc2]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_smul, Polynomial.map_C,
      ← Polynomial.derivative_map, e1, e2]
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    calc _ = C ((c1 : ℚ) * (c2 : ℚ)) *
            (a * map (Int.castRingHom ℚ) f + b * derivative (map (Int.castRingHom ℚ) f)) := by
          rw [C_mul]; simp only [eq_intCast]; ring
      _ = _ := by rw [hab, mul_one]; simp

theorem sep_int_poly_root_mod_prime_sq :
    ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable →
      ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  intro f hdeg hsep n
  obtain ⟨A, B, N, hN, hAB⟩ := int_bezout_derivative_of_separable f hsep
  obtain ⟨p, hp, hnp, x, hx⟩ := GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval f hdeg (max n N.natAbs)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hnp, ?_⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hev : A.eval x * f.eval x + B.eval x * (derivative f).eval x = N := by
    have := congrArg (Polynomial.eval x) hAB
    simpa using this
  have hpN : ¬ (p : ℤ) ∣ N := by
    intro h
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1
    have h3 := lt_of_le_of_lt (le_max_right n N.natAbs) hnp
    omega
  have hpd : ¬ (p : ℤ) ∣ (derivative f).eval x := by
    intro h
    apply hpN
    rw [← hev]
    exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right h _)
  have hcop : IsCoprime ((derivative f).eval x) (p : ℤ) := by
    rw [isCoprime_comm]
    exact (Prime.coprime_iff_not_dvd hpZ).mpr hpd
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨k, hk⟩ := hx
  obtain ⟨K, hK⟩ := Polynomial.binomExpansion f x ((p : ℤ) * (-(k * u)))
  refine ⟨x + (p : ℤ) * (-(k * u)), ?_⟩
  rw [hK, hk]
  refine ⟨k * v + K * (k * u) ^ 2, ?_⟩
  have : k = k * (u * (derivative f).eval x + v * p) := by rw [huv, mul_one]
  linear_combination (p : ℤ) * this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSqStatement
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  first | exact @GlobalTheory.sep_int_poly_root_mod_prime_sq | exact GlobalTheory.sep_int_poly_root_mod_prime_sq | (intros; apply GlobalTheory.sep_int_poly_root_mod_prime_sq <;> assumption)
end
end

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_integral_primitive_clearing : ∀ (K : Type) [Field K] [NumberField K], ∃ θ : K, IsIntegral ℤ θ ∧ 0 < (minpoly ℤ θ).natDegree ∧ ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable ∧ ∀ s : K, ∃ N : ℕ, 0 < N ∧ (N : K) * s ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
  intro K _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have halg : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  set θ : K := (y : K) * α with hθdef
  have hθ : IsIntegral ℤ θ := by rw [hθdef, ← zsmul_eq_mul]; exact hy
  refine ⟨θ, hθ, minpoly.natDegree_pos hθ, ?_, ?_⟩
  · rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθ]
    exact Algebra.IsSeparable.isSeparable ℚ θ
  · intro s
    set O := Algebra.adjoin ℤ ({θ} : Set K)
    have hθO : θ ∈ O := Algebra.subset_adjoin rfl
    have hs : s ∈ Algebra.adjoin ℚ ({α} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]
      trivial
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
      rw [hx]
      rcases Int.natAbs_eq y with h | h
      · have : ((y.natAbs : ℕ) : K) = (y : K) := (Int.cast_natCast (R := K) _).symm.trans (congrArg (Int.cast (R := K)) h.symm)
        rw [this]; exact hθO
      · have h' : (y.natAbs : ℤ) = -y := by omega
        have : ((y.natAbs : ℕ) : K) = -(y : K) := (Int.cast_natCast (R := K) _).symm.trans ((congrArg (Int.cast (R := K)) h').trans (Int.cast_neg y))
        rw [this, neg_mul]; exact O.neg_mem hθO
    | algebraMap q =>
      refine ⟨q.den, q.den_pos, ?_⟩
      have : ((q.den : ℕ) : K) * algebraMap ℚ K q = algebraMap ℤ K q.num := by
        rw [algebraMap_int_eq, eq_intCast, ← map_natCast (algebraMap ℚ K), ← map_mul,
          ← map_intCast (algebraMap ℚ K)]
        congr 1
        rw [mul_comm]; exact Rat.mul_den_eq_num q
      rw [this]; exact O.algebraMap_mem _
    | add a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a + b) = (M' : ℤ) • ((M : K) * a) + (M : ℤ) • ((M' : K) * b) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact O.add_mem (O.zsmul_mem hMa _) (O.zsmul_mem hMb _)
    | mul a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a * b) = ((M : K) * a) * ((M' : K) * b) := by
        push_cast; ring
      rw [this]
      exact O.mul_mem hMa hMb

theorem nonempty_adjoin_ringHom_zmod_of_dvd_eval : ∀ (K : Type) [Field K] [NumberField K] (θ : K), IsIntegral ℤ θ → ∀ (m : ℕ) (x : ℤ), (m : ℤ) ∣ (minpoly ℤ θ).eval x → Nonempty (Algebra.adjoin ℤ ({θ} : Set K) →+* ZMod m) := by
  intro K _ _ θ hθ m x hx
  have h : Polynomial.eval₂ (Int.castRingHom (ZMod m)) (x : ZMod m) (minpoly ℤ θ) = 0 := by
    rw [Polynomial.eval₂_at_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  exact ⟨(AdjoinRoot.lift (Int.castRingHom (ZMod m)) (x : ZMod m) h).comp (minpoly.equivAdjoin hθ).symm.toRingEquiv.toRingHom⟩

theorem nonempty_closure_ringHom_of_mul_mem : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (R : Type) [CommRing R] (ψ : O →+* R) (N : ℕ), 0 < N → IsUnit (N : R) → ∀ (S : Finset K), (∀ s ∈ S, (N : K) * s ∈ O) → Nonempty (Subring.closure (S : Set K) →+* R) := by
  intro K _ _ O R _ ψ N hN hu S hS
  set B := Localization.Away (N : O)
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hunits : ∀ m : Submonoid.powers (N : O), IsUnit (O.subtype m) := by
    rintro ⟨m, k, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hNK).pow k
  let φ : B →+* K := IsLocalization.lift (M := Submonoid.powers (N : O)) hunits
  have hφa : ∀ a : O, φ (algebraMap O B a) = (a : K) := fun a => IsLocalization.lift_eq hunits a
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (N : O)) b
    have h1 := congrArg φ (IsLocalization.mk'_spec B a m)
    rw [map_mul, hb, zero_mul, hφa] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    subst ha; exact IsLocalization.mk'_zero _
  have hle : Subring.closure (S : Set K) ≤ φ.range := by
    rw [Subring.closure_le]
    intro s hs
    refine ⟨IsLocalization.mk' B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)), ?_⟩
    have h1 := congrArg φ (IsLocalization.mk'_spec B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)))
    rw [map_mul, hφa, hφa] at h1
    simp only [map_natCast] at h1
    exact mul_right_cancel₀ hNK (h1.trans (mul_comm _ _))
  have hψN : IsUnit (ψ (N : O)) := by rw [map_natCast]; exact hu
  let χ : B →+* R := IsLocalization.Away.lift (N : O) hψN
  let e : B ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict ⟨fun x y h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact ⟨χ.comp (e.symm.toRingHom.comp (Subring.inclusion hle))⟩

theorem exists_prime_sq_ringHom_of_closure : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  intro K _ _ S n
  obtain ⟨θ, hθ, hdeg, hsep, hden⟩ := exists_integral_primitive_clearing K
  choose Nf hNf0 hNf using hden
  set N : ℕ := ∏ s ∈ S, Nf s with hN
  have hN0 : 0 < N := Finset.prod_pos (fun s _ => hNf0 s)
  have hNS : ∀ s ∈ S, (N : K) * s ∈ (Algebra.adjoin ℤ ({θ} : Set K)).toSubring := by
    intro s hs
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf hs
    have : (N : K) * s = (c : ℤ) • ((Nf s : K) * s) := by
      rw [hN, hc]; push_cast; rw [zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact Subalgebra.zsmul_mem _ (hNf s) _
  obtain ⟨p, hp, hlt, x, hx⟩ := GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable (minpoly ℤ θ) hdeg hsep (max n N)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hlt, ?_⟩
  obtain ⟨ψ⟩ := nonempty_adjoin_ringHom_zmod_of_dvd_eval K θ hθ (p ^ 2) x (by exact_mod_cast hx)
  have hu : IsUnit (N : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt hN0 (lt_of_le_of_lt (le_max_right _ _) hlt)
  exact nonempty_closure_ringHom_of_mul_mem K (Algebra.adjoin ℤ ({θ} : Set K)).toSubring (ZMod (p ^ 2)) ψ N hN0 hu S hNS

end GlobalTheory
