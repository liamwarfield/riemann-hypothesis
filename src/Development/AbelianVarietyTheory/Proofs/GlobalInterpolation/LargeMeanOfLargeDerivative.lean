module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTsumVonMangoldtDivRpowLeDiv
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

open ArithmeticFunction.vonMangoldt (residueClass LFunctionResidueClassAux LFunctionResidueClassAux_real
  eqOn_LFunctionResidueClassAux residueClass_apply_zero continuousOn_LFunctionResidueClassAux
  abscissaOfAbsConv_residueClass_le_one) in
theorem exists_tsum_vonMangoldt_div_rpow_le_div :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + s)) ∧
        ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + s) ≤ C / s := by
  have ha : IsUnit (1 : ZMod 1) := isUnit_one
  have hres : ∀ n : ℕ, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n = Λ n := fun n =>
    Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim (α := ZMod 1) _ _) _
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ x =
        (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re
          + ((Nat.totient 1 : ℕ) : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real ha hx,
      ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, ArithmeticFunction.vonMangoldt.residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have hc : ContinuousOn (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ)
      (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 1))
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x (hx : x ∈ Set.Icc (1 : ℝ) 2) ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨B, hB⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc hc
  refine ⟨|B| + 1, by linarith [abs_nonneg B], fun s hs hs1 => ⟨?_, ?_⟩⟩
  · have : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ (1 + s) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1 : ZMod 1)).trans_lt <| by
          have : (1 : ℝ) < 1 + s := by linarith
          exact_mod_cast this
    simpa only [hres] using this
  · have h1 := H (x := 1 + s) (by linarith)
    have h2 := hB _ (Set.mem_image_of_mem
      (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (show 1 + s ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩))
    simp only [hres, Nat.totient_one, Nat.cast_one, inv_one, add_sub_cancel_left] at h1
    rw [h1, add_div]
    have h3 : |B| ≤ |B| / s := by
      rw [le_div_iff₀ hs]
      exact mul_le_of_le_one_right (abs_nonneg B) hs1
    have h4 := le_abs_self B
    linarith

end GlobalTheory.Lin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableNonPrimeVonMangoldtDivRpow
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.NonPrimeVonMangoldt

private lemma log_div_pow_add_two_rpow_three_quarters_le (P : ℝ) (hP : 2 ≤ P) (k : ℕ) :
    Real.log P / (P ^ (k + 2)) ^ (3 / 4 : ℝ) ≤
      4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  have hP0 : 0 < P := by linarith
  have hA : 0 < P ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hP0 _
  have hC : 0 < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k := by positivity
  have hCB : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k ≤ (P ^ (3 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hP (by norm_num)) k
  have hsplit : (P ^ (k + 2)) ^ (3 / 4 : ℝ) = P ^ (3 / 2 : ℝ) * (P ^ (3 / 4 : ℝ)) ^ k := by
    rw [← Real.rpow_pow_comm hP0.le, pow_add, mul_comm, ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul hP0.le]
    norm_num
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show P ^ (1 / 4 : ℝ) / (1 / 4) = 4 * P ^ (1 / 4 : ℝ) by ring]
  have hrhs : 4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k
      = 4 * P ^ (1 / 4 : ℝ) / (P ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k) := by
    rw [show (-(5 / 4 : ℝ)) = 1 / 4 - 3 / 2 by norm_num, Real.rpow_sub hP0,
      Real.rpow_neg (by norm_num), inv_pow]
    field_simp
  rw [hsplit, hrhs]
  exact div_le_div₀ (by positivity) hlog (mul_pos hA hC) (mul_le_mul_of_nonneg_left hCB hA.le)

theorem _root_.GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  set F := (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) with hF
  set g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2) with hg_def
  have hg : Function.Injective g := by
    rintro ⟨p, k⟩ ⟨q, m⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 (h : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((m + 1) + 1))
    exact Prod.ext (Subtype.ext h1) (by simpa using h2)
  have hrange : ∀ n ∉ Set.range g, F n = 0 := by
    intro n hn
    by_cases hp : n.Prime
    · simp [hF, hp]
    by_cases hΛ : Λ n = 0
    · simp [hF, hΛ]
    exfalso
    apply hn
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hp')
    exact ⟨(⟨p, hp'⟩, k - 2), by simp only [hg_def]; congr 1; omega⟩
  rw [← hg.summable_iff hrange]
  have hmaj : Summable (fun pk : Nat.Primes × ℕ =>
      (4 * ((pk.1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ pk.2) := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) ?_ ?_ ?_ ?_
    · exact (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 4
    · exact summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_) hmaj
  · simp only [Function.comp_apply, hF]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  · obtain ⟨⟨p, hp⟩, k⟩ := pk
    have hnp : ¬ (p ^ (k + 2)).Prime := Nat.Prime.not_prime_pow (by omega)
    simp only [Function.comp_apply, hF, hg_def, if_neg hnp]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow]
    exact log_div_pow_add_two_rpow_three_quarters_le _ (by exact_mod_cast hp.two_le) k

end GlobalTheory.Lin.NonPrimeVonMangoldt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntervalIntegrableDivOfBounded
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

private lemma measurable_norm_sum_primesIoc (a : ℕ → ℂ) (x : ℝ) :
    Measurable (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) := by
  have h : (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) =
      (fun n : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ n).filter Nat.Prime, a p‖) ∘ Nat.floor := by
    funext t
    rfl
  rw [h]
  exact measurable_from_nat.comp Nat.measurable_floor

private lemma norm_sum_primesIoc_le_sum_range (a : ℕ → ℂ) (x y t : ℝ) (hty : t ≤ y) :
    ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖ := by
  refine (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
  intro n hn
  have hn' := (Finset.mem_filter.1 hn).1
  have h1 := (Finset.mem_Ioc.1 hn').2
  have h2 : ⌊t⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hty
  exact Finset.mem_range.2 (by omega)

private lemma integrableOn_norm_sum_primesIoc_pow_div (a : ℕ → ℂ) (x y : ℝ) (hx : 0 < x)
    (k : ℕ) :
    IntegrableOn (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) (Set.Icc x y) := by
  set B := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖
  refine Measure.integrableOn_of_bounded (M := B ^ k / x) (by simp)
    (((measurable_norm_sum_primesIoc a x).pow_const k).div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
  have ht0 : 0 < t := hx.trans_le ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div₀ (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_primesIoc_le_sum_range a x y t ht.2) k) hx ht.1

theorem _root_.GlobalTheory.Lin.sq_integral_primeSum_div_le (a : ℕ → ℂ) (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) ^ 2 ≤
      Real.log (y / x) * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
  have hx0 : 0 < x := by linarith
  have hI : ∀ k : ℕ, IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) volume x y := by
    intro k
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy]
    exact integrableOn_norm_sum_primesIoc_pow_div a x y hx0 k
  have hI1 : IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) volume x y := by
    simpa only [pow_one] using hI 1
  have hI0 : IntervalIntegrable (fun t : ℝ => 1 / t) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div continuousOn_id (fun t ht => ?_)
    rw [Set.uIcc_of_le hxy] at ht
    exact (hx0.trans_le ht.1).ne'
  have hlog : ∫ t in x..y, 1 / t = Real.log (y / x) := integral_one_div_of_pos hx0 (by linarith)
  have hquad : ∀ c : ℝ, 0 ≤ Real.log (y / x) * (c * c) +
      (-2 * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) * c +
      ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
    intro c
    have h0 : 0 ≤ ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t :=
      intervalIntegral.integral_nonneg hxy
        (fun t ht => div_nonneg (sq_nonneg _) (hx0.trans_le ht.1).le)
    have heq : ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t =
        (c * c) * (∫ t in x..y, 1 / t) -
          (2 * c) * (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) +
          ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hI0.const_mul _) (hI1.const_mul _),
        ← intervalIntegral.integral_add ((hI0.const_mul _).sub (hI1.const_mul _)) (hI 2)]
      congr 1
      funext t
      ring
    rw [heq, hlog] at h0
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

end GlobalTheory.Lin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPrimesIocEqSumIndicator
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem mem_primesIoc_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {p : ℕ} (hp : p ∈ primesIoc x y) :
    x < p ∧ (p : ℝ) ≤ y := by
  simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨(Nat.floor_lt hx).mp hp.1.1, (Nat.le_floor_iff (hx.trans hxy)).mp hp.1.2⟩

theorem sum_primesIoc_eq_sum_indicator (a : ℕ → ℂ) {x y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    ∑ p ∈ primesIoc x t, a p
      = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t := by
  have hs : primesIoc x t = (primesIoc x y).filter (fun p : ℕ => (p : ℝ) ≤ t) := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨h1, h2.trans (Nat.floor_mono hty)⟩, hp⟩, (Nat.le_floor_iff ht).mp h2⟩
    · rintro ⟨⟨⟨h1, _⟩, hp⟩, h3⟩
      exact ⟨⟨h1, (Nat.le_floor_iff ht).mpr h3⟩, hp⟩
  rw [hs, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : (p : ℝ) ≤ t <;> simp [h]

private lemma intervalIntegrable_indicator_Ici_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x y p : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume x y) :
    IntervalIntegrable ((Set.Ici p).indicator f) MeasureTheory.volume x y := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.indicator measurableSet_Ici

private lemma integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt {J J' : ℝ → ℝ} {x y p : ℝ} (hxp : x < p) (hpy : p ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y)) :
    ∫ t in x..y, (Set.Ici p).indicator (fun t => (J' t : ℂ)) t = (J y : ℂ) - J p := by
  have hxy : x ≤ y := hxp.le.trans hpy
  rw [intervalIntegral.integral_of_le hxy, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioc x y ∩ Set.Ici p = Set.Icc p y := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hxp.trans_le h1, h2⟩, h1⟩
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpy]
  have hsub : Set.uIcc p y ⊆ Set.Icc x y := by
    rw [Set.uIcc_of_le hpy]
    exact Set.Icc_subset_Icc hxp.le le_rfl
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hJ t (hsub ht)).ofReal_comp)
    ((hc'.mono hsub).intervalIntegrable)

theorem abel_primesIoc_weight (a : ℕ → ℂ) (J J' : ℝ → ℝ) (x y r : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y))
    (hb : ∀ t ∈ Set.Icc x y, |J' t| ≤ r / t) :
    ‖∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ)‖
      ≤ r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun t => ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t :=
    ⟨_, rfl⟩
  have hIcc : Set.uIcc x y = Set.Icc x y := Set.uIcc_of_le hxy
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hJi : IntervalIntegrable (fun t => (J' t : ℂ)) MeasureTheory.volume x y :=
    (hc'.mono hIcc.subset).intervalIntegrable
  have hterm : ∀ p ∈ primesIoc x y, IntervalIntegrable
      (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) MeasureTheory.volume x y :=
    fun p _ => (intervalIntegrable_indicator_Ici_of_intervalIntegrable hJi).const_mul (a p)
  have hpt : ∀ t, (J' t : ℂ) * S t
      = ∑ p ∈ primesIoc x y, a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t := by
    intro t
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : t ∈ Set.Ici (p : ℝ)
    · simp only [Set.indicator_of_mem h]
      ring
    · simp [Set.indicator_of_notMem h]
  have hL : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) = -∫ t in x..y, (J' t : ℂ) * S t := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum hterm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hb := mem_primesIoc_bounds hx0 hxy hp
    rw [intervalIntegral.integral_const_mul, integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt hb.1 hb.2 hJ hc]
    push_cast
    ring
  have hSi : IntervalIntegrable S MeasureTheory.volume x y := by
    have hS' : S = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) := by
      rw [hS]
      funext t
      simp [Finset.sum_apply]
    rw [hS']
    exact IntervalIntegrable.sum _ (fun p _ => intervalIntegrable_indicator_Ici_of_intervalIntegrable intervalIntegrable_const)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc x y) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [hIcc] at ht
    exact (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)).ne'
  have hg : IntervalIntegrable (fun t => r * (‖S t‖ / t)) MeasureTheory.volume x y := by
    have := (hSi.norm.mul_continuousOn hinv).const_mul r
    simpa [div_eq_mul_inv] using this
  have hf : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) MeasureTheory.volume x y := by
    have hsum := IntervalIntegrable.sum _ hterm
    have he : (fun t => (J' t : ℂ) * S t)
        = ∑ p ∈ primesIoc x y, (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) := by
      funext t
      rw [hpt, Finset.sum_apply]
    rw [← he] at hsum
    exact hsum.norm
  have hA : ∀ t ∈ Set.uIcc x y, ‖∑ p ∈ primesIoc x t, a p‖ / t = ‖S t‖ / t := by
    intro t ht
    rw [hIcc] at ht
    rw [sum_primesIoc_eq_sum_indicator a (hx0.trans ht.1) ht.2, hS]
  rw [hL, norm_neg, intervalIntegral.integral_congr hA, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
  refine intervalIntegral.integral_mono_on hxy hf hg (fun t ht => ?_)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |J' t| * ‖S t‖ ≤ r / t * ‖S t‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ = r * (‖S t‖ / t) := by ring

end GlobalTheory.Lin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeMeanOfLargeDerivative
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

noncomputable section

namespace GlobalTheory.Lin.LargeMean

def pw (k : ℕ) (u : ℝ) : ℝ := u ^ k / (k.factorial : ℝ) * Real.exp (-u)

lemma pw_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pw k u := by
  unfold pw; positivity

lemma pw_le (k : ℕ) {u θ : ℝ} (hu : 0 ≤ u) (hθ : 0 < θ) :
    pw k u ≤ θ ^ k * Real.exp (u / θ - u) := by
  have h := Real.pow_div_factorial_le_exp (u / θ) (by positivity) k
  have e : pw k u = θ ^ k * ((u / θ) ^ k / (k.factorial : ℝ) * Real.exp (-u)) := by
    unfold pw; rw [div_pow]; field_simp
  rw [e, sub_eq_add_neg, Real.exp_add]
  gcongr

lemma pw_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : pw k u ≤ 1 := by
  simpa using pw_le k hu one_pos

lemma pw_small (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (h : u ≤ δ / 3 * K) (hK : K ≤ k) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have h1 := pw_le k hu (θ := δ / 3) (by positivity)
  have h2 : u / (δ / 3) ≤ k := by
    rw [div_le_iff₀ (by positivity)]
    have : (K : ℝ) ≤ k := by exact_mod_cast hK
    nlinarith
  have h3 : Real.exp (u / (δ / 3) - u) ≤ 3 ^ k * Real.exp (-(u / 2)) := by
    have h4 : Real.exp k ≤ 3 ^ k := by
      rw [← mul_one (k : ℝ), Real.exp_nat_mul]
      gcongr
      exact (Real.exp_one_lt_d9.trans (by norm_num)).le
    calc _ ≤ Real.exp (k + -(u / 2)) := by gcongr; linarith
      _ ≤ _ := by rw [Real.exp_add]; gcongr
  calc _ ≤ (δ / 3) ^ k * (3 ^ k * Real.exp (-(u / 2))) := h1.trans (by gcongr)
    _ = _ := by rw [div_pow]; field_simp

lemma pw_large (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (h : 32 / δ * K ≤ u) (hK : k ≤ 2 * K) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have hu : 0 ≤ u := le_trans (by positivity) h
  have h1 := pw_le k hu (θ := 4) (by positivity)
  have hK' : (k : ℝ) ≤ 2 * K := by exact_mod_cast hK
  have h2 : (4 / δ) ^ k ≤ Real.exp (u / 4) := by
    calc (4 / δ) ^ k ≤ Real.exp (4 / δ) ^ k := by
          gcongr; linarith [Real.add_one_le_exp (4 / δ)]
      _ = Real.exp (k * (4 / δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          gcongr
          have : k * (4 / δ) ≤ 2 * K * (4 / δ) := by gcongr
          have e : 32 / δ * K = 4 * (2 * K * (4 / δ)) := by ring
          linarith
  have e : Real.exp (-(u / 2)) = Real.exp (u / 4) * Real.exp (u / 4 - u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ _ := h1
    _ = δ ^ k * ((4 / δ) ^ k * Real.exp (u / 4 - u)) := by rw [div_pow]; field_simp
    _ ≤ _ := by rw [e]; gcongr

lemma pw_pp (k : ℕ) {v r : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    pw k (r * v) ≤ (4 * r) ^ k * Real.exp (v / 4) := by
  have h1 := pw_le k (u := r * v) (by positivity) (θ := 4 * r) (by positivity)
  refine h1.trans ?_
  have : r * v / (4 * r) = v / 4 := by field_simp
  rw [this]
  gcongr
  have : 0 ≤ r * v := by positivity
  linarith

lemma hasDerivAt_pw (m : ℕ) (u : ℝ) : HasDerivAt (pw (m + 1)) (pw m u - pw (m + 1) u) u := by
  have h1 := ((hasDerivAt_pow (m + 1) u).div_const ((m + 1).factorial : ℝ)).mul
    (hasDerivAt_neg u).exp
  refine HasDerivAt.congr_deriv (f := pw (m + 1)) h1 ?_
  unfold pw
  rw [Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma continuous_pw (k : ℕ) : Continuous (pw k) := by
  unfold pw; fun_prop

lemma term_eq (c : ℕ → ℂ) (k n : ℕ) (r : ℝ) :
    (r : ℂ) ^ k * (((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((1 + r : ℝ) : ℂ))) = ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℂ) ^ (-((1 + r : ℝ) : ℂ)) = ((Real.exp (-(r * Real.log n)) / n : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow hn'.le]
    congr 1
    rw [Real.rpow_def_of_pos hn', eq_div_iff hn'.ne']
    nth_rewrite 2 [← Real.exp_log hn']
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  unfold pw
  push_cast
  ring

lemma rpow_form (n : ℕ) (hn : 0 < n) (s x : ℝ) :
    x / (n : ℝ) ^ (1 + s) = x / n * Real.exp (-(s * Real.log n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_def_of_pos hn', Real.exp_neg, mul_comm s]
  field_simp

lemma pointwise (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (n : ℕ) :
    ‖((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n -
      (if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0)‖ ≤
      δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) +
        (4 * r) ^ k * ((if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primesIoc]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have key : ∀ w : ℝ, 0 ≤ w → ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ Λ n / n * w := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hc n)
  have hpw : 0 ≤ pw k (r * Real.log n) := pw_nonneg k (by positivity)
  have fin : ∀ w : ℝ, 0 ≤ w → w ≤ δ ^ k * Real.exp (-(r * Real.log n / 2)) →
      ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) := by
    intro w hw h
    refine (key w hw).trans ?_
    rw [rpow_form n hn]
    calc _ ≤ Λ n / n * (δ ^ k * Real.exp (-(r * Real.log n / 2))) := by gcongr
      _ = _ := by ring_nf
  by_cases hp : n.Prime
  · simp only [hp, if_true, zero_div, mul_zero, add_zero]
    split_ifs with hm
    · rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le] at hm
      rw [Real.log_exp]
      have e0 : r * (32 / δ * K / r) = 32 / δ * K := by field_simp
      rw [e0]
      have e : ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n - (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (32 / δ * K) : ℝ) : ℂ) =
          ((Λ n / n * pw k (32 / δ * K) : ℝ) : ℂ) * c n := by
        rw [vonMangoldt_apply_prime hp]; push_cast; ring
      rw [e]
      refine fin _ (pw_nonneg k (by positivity)) ((pw_large K k hδ le_rfl h2).trans ?_)
      have h3 : Real.log n ≤ 32 / δ * K / r := by
        rw [Real.log_le_iff_le_exp hn']; exact hm.1.2
      rw [le_div_iff₀ hr] at h3
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    · rw [sub_zero]
      refine fin _ hpw ?_
      rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le,
        Nat.floor_lt (Real.exp_pos _).le] at hm
      by_cases h4 : Real.exp (δ / 3 * K / r) < n
      · have h5 : Real.exp (32 / δ * K / r) < n := by
          by_contra h6
          exact hm ⟨⟨h4, not_lt.mp h6⟩, hp⟩
        refine pw_large K k hδ ?_ h2
        have h3 := (Real.lt_log_iff_exp_lt hn').mpr h5
        rw [div_lt_iff₀ hr] at h3
        linarith
      · refine pw_small K k hδ (by positivity) ?_ h1
        have h3 := (Real.log_le_iff_le_exp hn').mpr (not_lt.mp h4)
        rw [le_div_iff₀ hr] at h3
        linarith
  · have hm : n ∉ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) := by
      rw [primesIoc, Finset.mem_filter]; exact fun h => hp h.2
    simp only [hp, hm, if_false, sub_zero]
    refine (key _ hpw).trans (le_add_of_nonneg_of_le (by positivity) ?_)
    have e : (3 / 4 : ℝ) = 1 + (-1 / 4) := by norm_num
    rw [e, rpow_form n hn]
    calc _ ≤ Λ n / n * ((4 * r) ^ k * Real.exp (Real.log n / 4)) := by
          gcongr; exact pw_pp k hr hl
      _ = _ := by ring_nf

lemma norm_tsum_le_of_close {T P : ℕ → ℂ} {G : ℕ → ℝ} (hP : Summable P)
    (hG : Summable G) (h : ∀ n, ‖T n - P n‖ ≤ G n) :
    ‖∑' n, T n‖ ≤ ‖∑' n, P n‖ + ∑' n, G n := by
  have h1 : Summable fun n => T n - P n := Summable.of_norm_bounded hG h
  have h2 : ∑' n, T n = ∑' n, P n + ∑' n, (T n - P n) := by
    rw [← hP.tsum_add h1]; simp
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact tsum_of_norm_bounded hG.hasSum h

lemma series_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r / 2)) :
    r ^ k * ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)),
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)‖ +
      (δ ^ k * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) +
        (4 * r) ^ k * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hq := GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow
  have hP := hasSum_sum_of_ne_finset_zero
    (s := primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)))
    (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0) (fun n hn => if_neg hn)
  have h := norm_tsum_le_of_close hP.summable ((hs.mul_left (δ ^ k)).add (hq.mul_left ((4 * r) ^ k)))
    (pointwise c hc hr hδ K k h1 h2)
  rw [hP.tsum_eq, (hs.mul_left _).tsum_add (hq.mul_left _), tsum_mul_left, tsum_mul_left,
    Finset.sum_congr rfl (fun n hn => if_pos hn)] at h
  refine le_of_eq_of_le ?_ h
  simp_rw [← term_eq]
  rw [tsum_mul_left, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, derSeries]

lemma abel_pw (a : ℕ → ℂ) {r x y : ℝ} (hr : 0 < r) (hx : 1 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    ‖∑ n ∈ primesIoc x y, a n *
        ((pw (m + 1) (r * Real.log n) - pw (m + 1) (r * Real.log y) : ℝ) : ℂ)‖ ≤
      r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  refine GlobalTheory.Lin.abel_primesIoc_weight a (fun t => pw (m + 1) (r * Real.log t))
    (fun t => (pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)) * (r * t⁻¹)) x y r hx hxy
    ?_ ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_pw m _).comp t ((Real.hasDerivAt_log ht0).const_mul r)
  · have hl : ContinuousOn (fun t => r * Real.log t) (Set.Icc x y) :=
      continuousOn_const.mul (continuousOn_id.log fun t ht => by
        have := ht.1; simp only [id]; linarith)
    refine (((continuous_pw m).comp_continuousOn hl).sub
      ((continuous_pw (m + 1)).comp_continuousOn hl)).mul
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => ?_))
    have := ht.1; simp only [id]; linarith
  · intro t ht
    have ht1 : 1 ≤ t := hx.trans ht.1
    have hu : 0 ≤ r * Real.log t := mul_nonneg hr.le (Real.log_nonneg ht1)
    have h1 : |pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [pw_nonneg m hu, pw_nonneg (m + 1) hu, pw_le_one m hu,
        pw_le_one (m + 1) hu]
    have h2 : 0 ≤ r * t⁻¹ := by have : 0 < t := by linarith
                                positivity
    rw [abs_mul, abs_of_nonneg h2, div_eq_mul_inv]
    exact mul_le_of_le_one_left h2 h1

theorem large_mean_of_large_derivative : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by
  intro A hA
  obtain ⟨C, hC, hCs⟩ := GlobalTheory.Lin.exists_tsum_vonMangoldt_div_rpow_le_div
  set B : ℝ := ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    positivity
  have hA0 : 0 < A := by linarith
  have hC0 : 0 < C := by linarith
  set η : ℝ := 1 / (16 * C * A) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  set δ : ℝ := A⁻¹ * η with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := mul_le_one₀ (inv_le_one_of_one_le₀ hA) hη0.le hη1
  have hab : δ / 3 < 32 / δ := by
    rw [div_lt_div_iff₀ (by norm_num) hδ0]; nlinarith
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  refine ⟨δ / 3, 32 / δ, 6 * Real.log A + 4 * (32 / δ), 1 / (8 * A * (B + 1)), 1, by positivity,
    hab, by positivity, by positivity, ?_⟩
  intro c r K k hc hr hr0 hK h1 h2 hD
  have hK1 : 1 ≤ K := by exact_mod_cast hK
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [le_div_iff₀ (by positivity)] at hr0
  have hrA : 8 * (r * A) ≤ 1 := by
    have : 0 ≤ r * A * B := by positivity
    nlinarith
  have hrB : 8 * (r * A * B) ≤ 1 := by
    have : 0 ≤ r * A := by positivity
    nlinarith
  have hr1 : r / 2 ≤ 1 := by nlinarith
  obtain ⟨hs, hsum⟩ := hCs (r / 2) (by positivity) hr1
  have hser := series_le c hc hr hδ0 K (m + 1) h1 h2 hs
  have hxy' : δ / 3 * K / r ≤ 32 / δ * K / r := by gcongr
  have hx : 1 ≤ Real.exp (δ / 3 * K / r) := Real.one_le_exp (by positivity)
  have hxy : Real.exp (δ / 3 * K / r) ≤ Real.exp (32 / δ * K / r) := Real.exp_le_exp.mpr hxy'
  have hab2 := abel_pw (fun p => (Real.log p : ℂ) * c p / p) hr hx hxy m
  have hcs := GlobalTheory.Lin.sq_integral_primeSum_div_le (fun p => (Real.log p : ℂ) * c p / p) _ _ hx hxy
  have hI2 : 0 ≤ ∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y :=
    intervalIntegral.integral_nonneg hxy fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  rw [← Real.exp_sub, Real.log_exp] at hcs
  rw [← hB] at hser
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y) = I₂ at *
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ / y) = I₁ at *
  set M : ℝ := A⁻¹ ^ (m + 1) * (A * r)⁻¹ with hM
  have hM0 : 0 < M := by positivity
  have e1 : M ≤ r ^ (m + 1) * ‖derSeries c (m + 1) ((1 + r : ℝ) : ℂ)‖ := by
    calc M = r ^ (m + 1) * (1 / (A * r) ^ (m + 1 + 1)) := by
          rw [hM, inv_pow, mul_pow]; field_simp; ring
      _ ≤ _ := by gcongr
  have e2 : δ ^ (m + 1) * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) ≤ M / 8 := by
    have h3 : η ^ (m + 1) ≤ η := pow_le_of_le_one hη0.le hη1 (by omega)
    calc _ ≤ δ ^ (m + 1) * (C / (r / 2)) := by gcongr
      _ = A⁻¹ ^ (m + 1) * η ^ (m + 1) * (C / (r / 2)) := by rw [hδ, mul_pow]
      _ ≤ A⁻¹ ^ (m + 1) * η * (C / (r / 2)) := by gcongr
      _ = M / 8 := by rw [hM, hη]; field_simp; ring
  have e3 : (4 * r) ^ (m + 1) * B ≤ M / 8 := by
    have h3 : 4 * r ≤ A⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hA0]
      have : 0 ≤ r * A := by positivity
      nlinarith
    have h4 : B ≤ (A * r)⁻¹ / 8 := by
      rw [inv_eq_one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ A⁻¹ ^ (m + 1) * ((A * r)⁻¹ / 8) := by gcongr
      _ = _ := by rw [hM]; ring
  have e4 : M / (2 * r) ≤ I₁ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e5 : (M / (2 * r)) ^ 2 ≤ (32 / δ * K / r) * I₂ := by
    calc _ ≤ I₁ ^ 2 := by gcongr
      _ ≤ _ := hcs
      _ ≤ _ := by
        gcongr
        have : 0 ≤ δ / 3 * K / r := by positivity
        linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have e6 : A ^ (2 * (m + 2)) * (4 * (32 / δ * K)) ≤
      Real.exp ((6 * Real.log A + 4 * (32 / δ)) * K) := by
    have h3 : A ^ (2 * (m + 2)) ≤ A ^ (6 * K) := pow_le_pow_right₀ hA (by omega)
    have h4 : A ^ (6 * K) = Real.exp (6 * Real.log A * K) := by
      nth_rewrite 1 [← Real.exp_log hA0]
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [add_mul, Real.exp_add, ← h4]
    gcongr
    linarith [Real.add_one_le_exp (4 * (32 / δ) * K)]
  rw [← div_le_iff₀' (by positivity)] at e5
  refine le_trans ?_ e5
  calc _ ≤ (A ^ (2 * (m + 2)) * (4 * (32 / δ * K)))⁻¹ / r ^ 3 := by
        rw [Real.exp_neg]; gcongr
    _ = _ := by
        rw [hM, inv_pow]; field_simp; ring

end GlobalTheory.Lin.LargeMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeMeanOfLargeDerivativeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_prime_sum_sq_ge_of_derSeries_large : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by
  first | exact @GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative | exact GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative | (intros; apply GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative <;> assumption)
end
