module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayCountThetaFibreCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumLamIdealLe
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LamRay

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_nonneg (I : Ideal (𝓞 K)) : 0 ≤ lamIdeal I := by
  unfold lamIdeal
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

theorem pow_prime_norm (hK : Module.finrank ℚ K = 2) {P : Ideal (𝓞 K)} {k : ℕ} (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hk : 1 ≤ k) : IsPrimePow (Ideal.absNorm (P ^ k)) ∧
      P ∣ Ideal.span {((Ideal.absNorm (P ^ k)).minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm P := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, h0⟩
  obtain ⟨p, hp, hm⟩ := GlobalTheory.Mem.FewPrimes.exists_prime_mem v
  have hd : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm P ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact absurd he h1.ne'
  have hik : i * k ≠ 0 := mul_ne_zero hi (by omega)
  rw [map_pow, he, ← pow_mul, hp.pow_minFac hik]
  exact ⟨(isPrimePow_nat_iff _).2 ⟨p, i * k, hp, Nat.pos_of_ne_zero hik, rfl⟩, hd, he ▸ h1⟩

theorem sum_lamIdeal_le (hK : Module.finrank ℚ K = 2) (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ 2 * Λ n := by
  set T := S.filter (fun I => ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) with hT
  have e : ∑ I ∈ S, lamIdeal I = ∑ I ∈ T, Real.log (Ideal.absNorm I.radical) := by
    rw [hT, Finset.sum_filter]
    rfl
  rw [e]
  rcases T.eq_empty_or_nonempty with h | ⟨I₀, hI₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg zero_le_two vonMangoldt_nonneg
  have key : ∀ I ∈ T, IsPrimePow n ∧ I.radical.IsPrime ∧ I.radical ≠ ⊥ ∧
      I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm I.radical ∧ ∃ k, I = I.radical ^ k := by
    intro I hI
    obtain ⟨hIS, P, k, hP, h0, hk, rfl⟩ := Finset.mem_filter.1 hI
    have h := pow_prime_norm hK hP h0 hk
    rw [hS _ hIS] at h
    rw [Ideal.radical_pow _ (by omega), hP.radical]
    exact ⟨h.1, hP, h0, h.2.1, h.2.2, k, rfl⟩
  have hn := (key I₀ hI₀).1
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  have hdvd : ∏ I ∈ T, I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun I hI J hJ hIJ => ?_) (fun I hI => (key I hI).2.2.2.1)
    obtain ⟨-, a1, a2, -, a3, k, a4⟩ := key I hI
    obtain ⟨-, b1, b2, -, -, l, b4⟩ := key J hJ
    refine Ideal.isCoprime_iff_sup_eq.2 ((a1.isMaximal a2).coprime_of_ne (b1.isMaximal b2) fun h => hIJ ?_)
    have c1 := hS I (Finset.mem_filter.1 hI).1
    have c2 := hS J (Finset.mem_filter.1 hJ).1
    rw [a4, map_pow] at c1
    rw [b4, map_pow, ← h] at c2
    have := Nat.pow_right_injective a3 (c1.trans c2.symm)
    rw [a4, b4, ← h, this]
  have h2 : ∏ I ∈ T, Ideal.absNorm I.radical ∣ n.minFac ^ 2 := by
    have := map_dvd Ideal.absNorm hdvd
    rwa [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at this
  have h3 : ((∏ I ∈ T, Ideal.absNorm I.radical : ℕ) : ℝ) ≤ (n.minFac ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.le_of_dvd (pow_pos hp.pos 2) h2)
  have hpos : ∀ I ∈ T, (0 : ℝ) < Ideal.absNorm I.radical := fun I hI =>
    Nat.cast_pos.2 (lt_trans one_pos (key I hI).2.2.2.2.1)
  push_cast at h3
  rw [← Real.log_prod (fun I hI => (hpos I hI).ne'), vonMangoldt_apply, if_pos hn]
  have h4 := Real.log_le_log (Finset.prod_pos hpos) h3
  rw [Real.log_pow] at h4
  exact_mod_cast h4


open QuadraticZeta in
theorem exists_gen {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) : ∃ ω : 𝓞 K, (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  have hsq : Squarefree d := hp.squarefree
  have hD := discr_eq_neg_of_sq_eq h2 hsq hd hr
  obtain ⟨w, bar, hw, -, hgen, hσ, σ, hσr⟩ :=
    ringOfIntegers_sqrt_neg_three_mod_four d hsq hd K h2 r hr
  refine ⟨w, hgen, fun a b => ?_⟩
  have h1 := norm_eq_sq h2 hD σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
  rw [← Algebra.coe_norm_int] at h1
  have h3 : σ (w : K) = (1 + Complex.I * √d) / 2 := by
    have := congrArg σ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hσr] at this
    linear_combination this / 2
  have h4 : σ (((a : 𝓞 K) + b * w : 𝓞 K) : K)
      = ((a + b / 2 : ℝ) : ℂ) + ((b * √d / 2 : ℝ) : ℂ) * Complex.I := by
    have h7 : (((a : 𝓞 K) + b * w : 𝓞 K) : K) = a + b * (w : K) := by simp
    rw [h7, map_add (f := _), map_mul, map_intCast, map_intCast, h3]
    push_cast
    ring
  rw [h4, Complex.sq_norm, Complex.normSq_add_mul_I] at h1
  have h5 : √(d : ℝ) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have h6 : ((Algebra.norm ℤ ((a : 𝓞 K) + b * w) : ℤ) : ℝ) * 4
      = (2 * a + b) ^ 2 + d * b ^ 2 := by
    push_cast at h1
    rw [h1]
    linear_combination (b : ℝ) ^ 2 * h5
  exact_mod_cast h6

theorem normOne_span {d M : ℕ} {ω : 𝓞 K} (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    GlobalTheory.Mem.An.NormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * ω := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  have h0 : 0 ≤ Algebra.norm ℤ π := by
    have : 0 ≤ (2 * (1 + (M : ℤ) * a) + M * b) ^ 2 + d * ((M : ℤ) * b) ^ 2 := by positivity
    linarith
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, Dvd.intro _ rfl, ⟨a, by ring⟩⟩
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg h0]
  linarith

theorem finite_idealsIn {M : ℕ} (D : RayData K M) (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

theorem lamRay_props : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, (∀ g n, 0 ≤ lamRay D g n) ∧ (∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) ∧ ∀ p : ℕ, p.Prime → lamRay D 1 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro K _ _ d M x hp hd _ hx hK _ D
  refine ⟨fun g n => ?_, fun n => ?_, fun p _ h => ?_⟩
  · exact finsum_nonneg fun I => finsum_nonneg fun _ => lamIdeal_nonneg I
  · have e : ∀ g, lamRay D g n = ∑ I ∈ (finite_idealsIn D g n).toFinset, lamIdeal I := fun g =>
      finsum_mem_eq_finite_toFinset_sum _ _
    simp only [e]
    rw [← Finset.sum_biUnion]
    · refine sum_lamIdeal_le hK n _ fun I hI => ?_
      obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hI
      exact ((Set.Finite.mem_toFinset _).1 hg).2.2.1
    · intro g _ g' _ hgg
      refine Finset.disjoint_left.2 fun I h1 h2 => hgg ?_
      exact ((Set.Finite.mem_toFinset _).1 h1).2.2.2.symm.trans ((Set.Finite.mem_toFinset _).1 h2).2.2.2
  · have hne : (idealsIn D 1 p).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      apply h
      unfold lamRay
      rw [h0, finsum_mem_empty]
    obtain ⟨I, h0, hc, hN, hcl⟩ := hne
    obtain ⟨a, b, ha, -, ha1, hb1, hab⟩ := (D.cls_eq_one_iff hc h0).1 hcl
    have hb : b ∈ Ideal.span {a} := by
      have : Ideal.span {b} ≤ Ideal.span {a} := hab ▸ Ideal.mul_le_left
      exact this (Ideal.mem_span_singleton_self b)
    obtain ⟨π, rfl⟩ := Ideal.mem_span_singleton.1 hb
    rw [← Ideal.span_singleton_mul_span_singleton] at hab
    have hI : I = Ideal.span {π} :=
      mul_left_cancel₀ (by simpa [Ideal.span_singleton_eq_bot] using ha) hab
    have hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have : π - 1 = (a * π - 1) - π * (a - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ hb1 (Ideal.mul_mem_left _ _ ha1)
    obtain ⟨ω, hgen, hnorm⟩ := exists_gen hp hd hx hK
    rw [← hN, hI]
    exact normOne_span hgen hnorm hπ

end GlobalTheory.Hk.LamRay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConvRealChar
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

noncomputable section

namespace GlobalTheory.Hk.RaySq

variable {K : Type} [Field K] [NumberField K]

def normEq (K : Type) [Field K] [NumberField K] (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset

lemma mem_normEq {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normEq K n ↔ Ideal.absNorm I = n := by
  simp [normEq]

def dv (C : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm C)).toFinset).filter (· ∣ C)

lemma mem_dv {C J : Ideal (𝓞 K)} (hC : C ≠ 0) : J ∈ dv C ↔ J ∣ C := by
  simp only [dv, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
  intro h
  have hC' : Ideal.absNorm C ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hC
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hC') (map_dvd Ideal.absNorm h)

def r (f : Ideal (𝓞 K) → ℝ) (C : Ideal (𝓞 K)) : ℝ := ∑ J ∈ dv C, f J

private lemma dvd_of_dvd_prime_pow_mul' {P C J : Ideal (𝓞 K)} (hP : Prime P) (hJ : ¬ P ∣ J) :
    ∀ k : ℕ, J ∣ P ^ k * C → J ∣ C := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    apply ih
    obtain ⟨Y, hY⟩ := h
    have hPY : P ∣ J * Y := ⟨P ^ k * C, by rw [← hY]; ring⟩
    rcases hP.dvd_or_dvd hPY with h1 | ⟨Y', rfl⟩
    · exact absurd h1 hJ
    · refine ⟨Y', ?_⟩
      apply mul_left_cancel₀ hP.ne_zero
      calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        _ = J * (P * Y') := hY
        _ = P * (J * Y') := by ring

lemma r_step (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ (k + 1) * C) = f P * r f (P ^ k * C) + r f C := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hA : P ^ (k + 1) * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hB : P ^ k * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hsplit : dv (P ^ (k + 1) * C) = dv C ∪ (dv (P ^ k * C)).image (P * ·) := by
    ext J
    rw [Finset.mem_union, Finset.mem_image, mem_dv hA, mem_dv hC]
    constructor
    · intro h
      by_cases hJ : P ∣ J
      · right
        obtain ⟨J', rfl⟩ := hJ
        refine ⟨J', (mem_dv hB).2 ?_, rfl⟩
        obtain ⟨Y, hY⟩ := h
        refine ⟨Y, mul_left_cancel₀ hP0 ?_⟩
        calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
          _ = P * J' * Y := hY
          _ = P * (J' * Y) := by ring
      · left
        exact dvd_of_dvd_prime_pow_mul' hP hJ (k + 1) h
    · rintro (h | ⟨J', hJ', rfl⟩)
      · exact h.trans ⟨P ^ (k + 1), by ring⟩
      · rw [mem_dv hB] at hJ'
        have e : P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        rw [← e]
        exact mul_dvd_mul_left P hJ'
  have hdisj : Disjoint (dv C) ((dv (P ^ k * C)).image (P * ·)) := by
    rw [Finset.disjoint_left]
    intro J hJ hJ'
    rw [mem_dv hC] at hJ
    obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hJ'
    exact hPC ((dvd_mul_right P J').trans hJ)
  unfold r
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hP0 hab)]
  simp only [hf, ← Finset.mul_sum]
  ring

lemma r_pow (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ k * C) = (∑ i ∈ Finset.range (k + 1), f P ^ i) * r f C := by
  have hg : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), f P ^ i = f P * ∑ i ∈ Finset.range m, f P ^ i + 1 := by
    intro m
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ', pow_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [r_step f hf hP hC hPC k, ih, hg (k + 1)]
    ring

private lemma sum_range_neg_one_pow_eq_ite (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', h.neg_one_pow]
      norm_num
    · have h' : Even (n + 1) := Nat.even_add_one.2 h
      rw [if_neg h, if_pos h', (Nat.not_even_iff_odd.1 h).neg_one_pow]
      norm_num

lemma geom_bounds {x : ℝ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), x ^ i ∧ 1 ≤ ∑ i ∈ Finset.range (2 * k + 1), x ^ i := by
  rcases hx with rfl | rfl | rfl
  · simp [Finset.sum_range_succ']
  · simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine ⟨by positivity, ?_⟩
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rw [sum_range_neg_one_pow_eq_ite, sum_range_neg_one_pow_eq_ite]
    have h : ¬ Even (2 * k + 1) := by
      rw [Nat.even_add_one, not_not]
      exact even_two_mul k
    rw [if_neg h]
    refine ⟨?_, le_refl _⟩
    split_ifs <;> norm_num

lemma r_one (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) : r f 1 = 1 := by
  have hd : dv (1 : Ideal (𝓞 K)) = {1} := by
    ext J
    rw [mem_dv one_ne_zero, Finset.mem_singleton, Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff]
  unfold r
  rw [hd, Finset.sum_singleton, h1]

lemma r_bounds (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) (hf : ∀ I J, f (I * J) = f I * f J)
    (hv : ∀ I, f I = 0 ∨ f I = 1 ∨ f I = -1) (C : Ideal (𝓞 K)) (hC : C ≠ 0) : 0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) := by
  suffices h : ∀ N : ℕ, ∀ C : Ideal (𝓞 K), C ≠ 0 → Ideal.absNorm C = N →
      0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) from h _ C hC rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hN
  by_cases hu : IsUnit C
  · obtain rfl : C = 1 := isUnit_iff_eq_one.1 hu
    rw [one_pow, r_one f h1]
    norm_num
  · obtain ⟨P, hPirr, hPC⟩ := WfDvdMonoid.exists_irreducible_factor hu hC
    have hP : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.1 hPirr
    obtain ⟨k, D, hPD, rfl⟩ := WfDvdMonoid.max_power_factor hC hPirr
    have hD : D ≠ 0 := by
      rintro rfl
      exact hC (mul_zero _)
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hPC
      exact hPD hPC
    have hN2 : 2 ≤ Ideal.absNorm P := by
      have h0 : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact hP.ne_zero
      have h1' : Ideal.absNorm P ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]
        intro h
        apply hPirr.not_isUnit
        rw [h, ← Ideal.one_eq_top]
        exact isUnit_one
      omega
    have hD0 : 0 < Ideal.absNorm D := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hD
    have hlt : Ideal.absNorm D < N := by
      rw [← hN, map_mul, map_pow]
      have h2 : 2 ≤ Ideal.absNorm P ^ k := le_trans hN2 (Nat.le_self_pow hk _)
      nlinarith
    obtain ⟨ihD1, ihD2⟩ := ih _ hlt D hD rfl
    have hPD2 : ¬ P ∣ D ^ 2 := by
      rw [pow_two]
      intro h
      rcases hP.dvd_or_dvd h with h | h <;> exact hPD h
    have hD2 : D ^ 2 ≠ 0 := pow_ne_zero _ hD
    obtain ⟨g1, g2⟩ := geom_bounds (hv P) k
    constructor
    · rw [r_pow f hf hP hD hPD k]
      exact mul_nonneg g1 ihD1
    · have e : (P ^ k * D) ^ 2 = P ^ (2 * k) * D ^ 2 := by ring
      rw [e, r_pow f hf hP hD2 hPD2 (2 * k)]
      exact one_le_mul_of_one_le_of_one_le g2 ihD2

lemma conv_eq (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J =
      ∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J := by
  have L : (∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J) =
      ∑ y ∈ n.divisorsAntidiagonal.sigma (fun p => normEq K p.1 ×ˢ normEq K p.2),
        F (y.2.1 * y.2.2) y.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_product]
  have R : (∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J) =
      ∑ y ∈ (normEq K n).sigma (fun C => dv C), F y.1 y.2 := by
    rw [Finset.sum_sigma]
  rw [L, R]
  refine Finset.sum_nbij'
    (fun y : (Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K)) =>
      (⟨y.2.1 * y.2.2, y.2.2⟩ : Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)))
    (fun y : (Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)) =>
      (⟨(Ideal.absNorm y.1 / Ideal.absNorm y.2, Ideal.absNorm y.2),
        ((if h : y.2 ∣ y.1 then Exists.choose h else 0), y.2)⟩ :
        Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy ⊢
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hIJ0 : I * J ≠ 0 := by
      intro h
      have e := congrArg Ideal.absNorm h
      rw [map_mul, _root_.map_zero, hI, hJ, hab] at e
      exact hn e
    exact ⟨by rw [map_mul, hI, hJ, hab], (mem_dv hIJ0).2 (dvd_mul_left J I)⟩
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dite_eq_left (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq]
    rw [hch, map_mul, Nat.mul_div_cancel_left _ hNJ]
    rw [map_mul] at hCn
    exact ⟨⟨by rw [mul_comm]; exact hCn, hn⟩, rfl, trivial⟩
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hJ0 : J ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hJ
      subst hJ
      exact hn (by rw [← hab, mul_zero])
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    have hch : (if h : J ∣ I * J then Exists.choose h else 0) = I := by
      rw [dite_eq_left (dvd_mul_left J I)]
      apply mul_left_cancel₀ hJ0
      rw [← Exists.choose_spec (dvd_mul_left J I), mul_comm]
    dsimp only
    rw [hch, map_mul, Nat.mul_div_cancel _ hNJ, hI, hJ]
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dite_eq_left (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    dsimp only
    rw [hch, mul_comm]
  · rintro ⟨p, I, J⟩ _
    rfl

variable {M : ℕ} (D : RayData K M)

def chi (ε : D.G → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then ε (D.cls I) else 0

lemma sum_aRay (ε : D.G → ℝ) (n : ℕ) : ∑ g, ε g * aRay D g n = ∑ I ∈ normEq K n, chi D ε I := by
  have hcard : ∀ g, aRay D g n = (((normEq K n).filter (fun I =>
      (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g)).card : ℝ) := by
    intro g
    unfold aRay
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext I
    simp only [idealsIn, Finset.coe_filter, Set.mem_setOf_eq, mem_normEq]
    tauto
  have hchi : ∀ I, chi D ε I = ∑ g, if (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g
      then ε g else 0 := by
    intro I
    by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · rw [chi, if_pos h]
      simp only [ite_and, if_pos h]
      simp
    · rw [chi, if_neg h]
      simp only [ite_and, if_neg h, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun I _ => hchi I), Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard g, mul_comm]

lemma chi_mul (ε : D.G → ℝ) (hε : ∀ g h, ε (g * h) = ε g * ε h) (I J : Ideal (𝓞 K)) :
    chi D ε (I * J) = chi D ε I * chi D ε J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J (Ideal.span {(M : 𝓞 K)})
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}) :=
        ⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      simp only [chi]
      rw [if_pos hIJ, if_pos hI, if_pos hJ, D.cls_mul I J hI.2 hJ.2 hI.1 hJ.1, hε]
    · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
        rintro ⟨h1, h2⟩
        exact hJ ⟨fun h => h1 (by rw [h, Ideal.mul_bot]), h2.of_mul_left_right⟩
      simp only [chi]
      rw [if_pos hI, if_neg hJ, if_neg hIJ, mul_zero]
  · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
      rintro ⟨h1, h2⟩
      exact hI ⟨fun h => h1 (by rw [h, Ideal.bot_mul]), h2.of_mul_left_left⟩
    simp only [chi]
    rw [if_neg hI, if_neg hIJ, zero_mul]

lemma chi_one (ε : D.G → ℝ) (h1 : ε 1 = 1) : chi D ε 1 = 1 := by
  have hc : IsCoprime (1 : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)}) := isCoprime_one_left
  have hb : (1 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ideal.one_eq_top]
    exact top_ne_bot
  have hcls : D.cls 1 = 1 := by
    have e := D.cls_mul 1 1 hc hc hb hb
    rw [one_mul] at e
    exact mul_left_cancel (by rw [mul_one]; exact e.symm : D.cls 1 * D.cls 1 = D.cls 1 * 1)
  rw [chi, if_pos ⟨hb, hc⟩, hcls, h1]

lemma conv_aRay (ε : D.G → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 =
      ∑ C ∈ normEq K n, chi D (fun _ => 1) C * r (chi D ε) C := by
  have h1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  have hkey : ∀ I J : Ideal (𝓞 K),
      chi D (fun _ => 1) I * chi D ε J = chi D (fun _ => 1) (I * J) * chi D ε J := by
    intro I J
    rw [chi_mul D (fun _ => 1) (fun _ _ => (mul_one 1).symm) I J, mul_assoc]
    congr 1
    simp only [chi]
    split_ifs <;> simp
  calc _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2,
        chi D (fun _ => 1) (I * J) * chi D ε J := by
        simp_rw [h1, sum_aRay D ε, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun J _ => hkey I J
    _ = _ := (conv_eq (fun C J => chi D (fun _ => 1) C * chi D ε J) hn).trans
        (by simp only [r, Finset.mul_sum])

theorem conv_real_char : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (ε : D.G → ℝ), ε 1 = 1 → (∀ g h, ε (g * h) = ε g * ε h) → (∀ g, ε g = 1 ∨ ε g = -1) → ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 ∧ ∑ g, aRay D g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 := by
  intro K _ _ M _ D ε h1 hmul hpm n
  have hv : ∀ I, chi D ε I = 0 ∨ chi D ε I = 1 ∨ chi D ε I = -1 := by
    intro I
    unfold chi
    split_ifs
    · rcases hpm (D.cls I) with h | h <;> simp [h]
    · simp
  have hr : ∀ C : Ideal (𝓞 K), C ≠ 0 → 0 ≤ r (chi D ε) C ∧ 1 ≤ r (chi D ε) (C ^ 2) :=
    fun C hC => r_bounds (chi D ε) (chi_one D ε h1) (chi_mul D ε hmul) hv C hC
  have h01 : ∀ I, chi D (fun _ => 1) I =
      if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then 1 else 0 := fun I => rfl
  have hterm : ∀ C : Ideal (𝓞 K), 0 ≤ chi D (fun _ => 1) C * r (chi D ε) C := by
    intro C
    rw [h01]
    split_ifs with h
    · rw [one_mul]
      exact (hr C h.1).1
    · rw [zero_mul]
  have hsum1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, ?_⟩
    have h0 : ∑ I ∈ normEq K 0, chi D (fun _ => 1) I = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      rw [mem_normEq, Ideal.absNorm_eq_zero_iff] at hI
      simp [chi, hI]
    rw [hsum1, h0]
    simp
  · have hn0 : n ≠ 0 := hn.ne'
    rw [conv_aRay D ε hn0, conv_aRay D ε (pow_ne_zero 2 hn0), hsum1]
    refine ⟨Finset.sum_nonneg fun C _ => hterm C, ?_⟩
    calc ∑ I ∈ normEq K n, chi D (fun _ => 1) I
        ≤ ∑ I ∈ normEq K n, chi D (fun _ => 1) (I ^ 2) * r (chi D ε) (I ^ 2) := by
          refine Finset.sum_le_sum fun I _ => ?_
          by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
          · have h2 : I ^ 2 ≠ ⊥ ∧ IsCoprime (I ^ 2) (Ideal.span {(M : 𝓞 K)}) :=
              ⟨pow_ne_zero 2 h.1, h.2.pow_left⟩
            rw [h01, h01, if_pos h, if_pos h2, one_mul]
            exact (hr I h.1).2
          · rw [h01 I, if_neg h]
            exact hterm (I ^ 2)
      _ = ∑ C ∈ (normEq K n).image (· ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          have hab' : a ^ 2 = b ^ 2 := hab
          exact dvd_antisymm ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.dvd)
            ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.symm.dvd)
      _ ≤ ∑ C ∈ normEq K (n ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun C _ _ => hterm C
          intro C hC
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hC
          rw [mem_normEq] at hI ⊢
          rw [map_pow, hI]

end GlobalTheory.Hk.RaySq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteIdealsIn
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayConv

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_pow {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    lamIdeal (P ^ (k + 1)) = Real.log (Ideal.absNorm P) := by
  have h1 : P.IsPrime := Ideal.isPrime_of_prime hP
  unfold lamIdeal
  rw [if_pos ⟨P, k + 1, h1, hP.ne_zero, by omega, rfl⟩, Ideal.radical_pow _ (by omega), h1.radical]

theorem finite_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)

theorem sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
    intro _ T hT
    have h1 : I = 1 := isUnit_iff_eq_one.1 hu
    subst h1
    rw [map_one, Nat.cast_one, Real.log_one]
    refine Finset.sum_eq_zero fun J hJ => ?_
    unfold lamIdeal
    rw [if_neg]
    rintro ⟨P, k, hP, hP0, hk, rfl⟩
    have := isUnit_of_dvd_one ((hT _).1 hJ)
    rw [isUnit_pow_iff (by omega), Ideal.isUnit_iff] at this
    exact hP.ne_top this
  | h₃ I P hI hP ih =>
    intro _ T hT
    set S := (finite_dvd hI).toFinset with hS
    have hSm : ∀ J, J ∈ S ↔ J ∣ I := fun J => by simp [hS]
    have hsub : S ⊆ T := fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)
    have hfin : FiniteMultiplicity P I := FiniteMultiplicity.of_prime_left hP hI
    have hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0 := fun J hJ =>
      Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
    rw [← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]
    · rw [Finset.mem_sdiff, hT, hSm]
      refine ⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
      rw [pow_succ']
      exact mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)
    · intro J hJ hne
      rw [Finset.mem_sdiff, hT, hSm] at hJ
      unfold lamIdeal
      rw [if_neg]
      rintro ⟨Q, k, hQ, hQ0, hk, rfl⟩
      have hQp : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
      by_cases hQP : Q = P
      · subst hQP
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 : Q ^ j ∣ I := by
          have := hJ.1
          rw [pow_succ'] at this
          exact (mul_dvd_mul_iff_left hP.ne_zero).1 this
        have h2 : j ≤ multiplicity Q I := hfin.le_multiplicity_of_pow_dvd h1
        have h3 : ¬ j + 1 ≤ multiplicity Q I := fun h => hJ.2 (pow_dvd_of_le_multiplicity h)
        exact hne (by rw [show j = multiplicity Q I by omega])
      · refine hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)
        intro hd
        exact hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))

variable {M : ℕ} (D : RayData K M)

theorem finite_idealsIn (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

end GlobalTheory.Hk.RayConv

namespace GlobalTheory.Hk


open RayConv in
theorem aRay_mul_log : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (finite_idealsIn D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dite_eq_right hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]
  · intro x _; rfl

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRay
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

section

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

theorem aRay_norm_zero (g : D.G) : aRay D g 0 = 0 := by
  have : idealsIn D g 0 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h2, -⟩
    exact h1 (Ideal.absNorm_eq_zero_iff.1 h2)
  simp [aRay, this]

theorem aRay_one_norm_one : aRay D 1 1 = 1 := by
  have : idealsIn D 1 1 = {⊤} := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, -, h2, -⟩
      exact Ideal.absNorm_eq_one_iff.1 h2
    · rintro rfl
      refine ⟨top_ne_bot, ?_, Ideal.absNorm_eq_one_iff.2 rfl, D.cls_top⟩
      rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  simp [aRay, this]

theorem aRay_norm_one_of_ne {g : D.G} (hg : g ≠ 1) : aRay D g 1 = 0 := by
  have : idealsIn D g 1 = ∅ := by
    ext I
    simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, h2, h3⟩
    rw [Ideal.absNorm_eq_one_iff.1 h2, D.cls_top] at h3
    exact hg h3.symm
  simp [aRay, this]

theorem card_ray_le (hK : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ 4 * |(discr K : ℝ)| * (M : ℝ) ^ 2 := by
  have h1 := RayData.card_eq_rayNo K M hM D
  have h2 := (RayNo.rayNo_bounds K (Ideal.span {(M : 𝓞 K)})
    (by simpa [Ideal.span_singleton_eq_bot] using hM)).2.1
  have h3 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton, show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) M by simp, Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK]
    simp [Int.natAbs_pow]
  have h4 : (classNumber K : ℝ) ≤ 4 * |(discr K : ℝ)| := by
    exact_mod_cast GlobalTheory.classNumber_le_four_mul_abs_discr K hK
  rw [h3, ← h1] at h2
  have h5 : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2 := by exact_mod_cast h2
  exact h5.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

end

theorem addChar_eq_one_or_neg_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    rw [← AddChar.mul_apply, h, AddChar.one_apply]
  exact mul_self_eq_one_iff.1 this

theorem exists_lFam_ray : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧
    ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro d M hd hd4 hd100 hM
  obtain ⟨K, _, _, ω, -, hK, hdisc, hω, -, -⟩ := GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hd hd4
  have hx : (((2 * ω - 1 : 𝓞 K) : K)) ^ 2 = -(d : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hω
    simpa using this
  have hM0 : M ≠ 0 := by omega
  let D : RayData K M := rayData K M hM0
  have hc := GlobalTheory.Hk.rayCountTheta K d M _ hd hd4 hd100 hx hK hM D
  have hl := GlobalTheory.Hk.LamRay.lamRay_props K d M _ hd hd4 hd100 hx hK hM D
  have hcard := card_ray_le D hK hM0
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hsd : Real.sqrt d ≤ d := by nlinarith
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rw [hdisc] at hcard
  have habs : |(((-(d : ℤ) : ℤ)) : ℝ)| = d := by
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
  rw [habs] at hcard
  refine ⟨{
    G := Additive D.G
    ft := D.fin
    B := 4 * (d : ℝ) * (M : ℝ) ^ 2
    κ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2)
    a := fun g n => aRay D g.toMul n
    lam := fun g n => lamRay D g.toMul n
    B_ge := by nlinarith
    card_le := hcard
    κ_ge := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Real.sqrt d * (M : ℝ) ^ 2 ≤ d * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsd (by positivity)
      have h2 : (0 : ℝ) ≤ d * (M : ℝ) ^ 2 := by positivity
      nlinarith
    κ_le := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    a_nonneg := fun g n => Nat.cast_nonneg _
    a_zero := fun g => aRay_norm_zero D _
    a_one := aRay_one_norm_one D
    a_one_ne := fun g hg => aRay_norm_one_of_ne D hg
    count := fun g => (hc g.toMul).1
    theta := fun g => (hc g.toMul).2
    lam_nonneg := fun g n => hl.1 _ n
    lam_le := hl.2.1
    conv := fun g n => GlobalTheory.Hk.aRay_mul_log K M (by omega) D g.toMul n
    sq := fun χ hχ n => GlobalTheory.Hk.RaySq.conv_real_char K M (by omega) D (fun g => (χ (Additive.ofMul g)).re) (by simp) ?_ ?_ n }, rfl, hl.2.2⟩
  · intro g h
    rw [ofMul_mul, AddChar.map_add_eq_mul]
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]
  · intro g
    rcases addChar_eq_one_or_neg_one χ hχ (Additive.ofMul g) with h1 | h1 <;> simp [h1]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRayStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧ ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  first | exact @GlobalTheory.Hk.exists_lFam_ray | exact GlobalTheory.Hk.exists_lFam_ray | (intros; apply GlobalTheory.Hk.exists_lFam_ray <;> assumption)
end
