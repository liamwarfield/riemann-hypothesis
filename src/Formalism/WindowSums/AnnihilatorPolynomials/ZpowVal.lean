module

public import Formalism.WindowSums.Statement

@[expose] public section

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
namespace Formalism.WindowSums

open Finset

section ZpowValAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma zv_prime : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p

lemma zv_emult_eq_val {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit (Units.isUnit _),
    zero_add, emultiplicity_pow_self_of_prime zv_prime]

lemma zv_emult_unit_mul {c : ℤ_[ℓ]} (hc : IsUnit c) (y : ℤ_[ℓ]) :
    emultiplicity (ℓ : ℤ_[ℓ]) (c * y) = emultiplicity (ℓ : ℤ_[ℓ]) y := by
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit hc, zero_add]

lemma zv_not_dvd_of_dvd_sub_one {x : ℤ_[ℓ]} (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1) : ¬ (ℓ : ℤ_[ℓ]) ∣ x := by
  intro h
  have h1 : (ℓ : ℤ_[ℓ]) ∣ 1 := by
    have h2 := dvd_sub h hx
    rwa [sub_sub_cancel] at h2
  exact zv_prime.not_unit (isUnit_of_dvd_one h1)

lemma zv_two_sq_step (h2 : ℓ = 2) {x : ℤ_[ℓ]} (h4 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ 2 - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + 1 := by
  have hx1 : (ℓ : ℤ_[ℓ]) ∣ x - 1 := (dvd_pow_self _ two_ne_zero).trans h4
  have e : x + 1 = (x - 1) + (ℓ : ℤ_[ℓ]) := by
    have hc : (ℓ : ℤ_[ℓ]) = 2 := by
      have h7 := congrArg (fun n : ℕ => (n : ℤ_[ℓ])) h2
      simpa using h7
    rw [hc]
    ring

  have hp1 : emultiplicity (ℓ : ℤ_[ℓ]) (x + 1) = 1 := by
    rw [← Nat.cast_one (R := ℕ∞), emultiplicity_eq_coe]
    refine ⟨by rw [pow_one, e]; exact dvd_add hx1 dvd_rfl, fun hd => ?_⟩
    have h3 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ (ℓ : ℤ_[ℓ]) ^ 1 := by
      have h5 := dvd_sub hd h4
      rw [e, add_sub_cancel_left] at h5
      rw [pow_one]
      exact h5
    have h6 := (pow_dvd_pow_iff zv_prime.ne_zero zv_prime.not_unit).1 h3
    omega
  rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, emultiplicity_mul zv_prime, hp1]

lemma zv_pow_prime_pow (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) (k : ℕ) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ ℓ ^ k - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + k := by
  by_cases hl : ℓ = 2
  · have h4 := h2 hl
    induction k with
    | zero => simp
    | succ k ih =>
      have hy : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x ^ ℓ ^ k - 1 := h4.trans (sub_one_dvd_pow_sub_one x _)
      have e : x ^ ℓ ^ (k + 1) = (x ^ ℓ ^ k) ^ 2 := by
        rw [pow_succ, pow_mul]
        exact congrArg (fun n => (x ^ ℓ ^ k) ^ n) hl
      rw [e, zv_two_sq_step hl hy, ih]
      push_cast
      ring
  · have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hl
    have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (x := x) (y := 1) zv_prime hodd
      (by simpa using hx) (zv_not_dvd_of_dvd_sub_one hx) k
    rwa [one_pow] at h1

lemma zv_not_dvd_cast {m : ℕ} (hm : ¬ ℓ ∣ m) : ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
  intro h
  rw [← PadicInt.norm_lt_one_iff_dvd] at h
  have h' : ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
    rw [Int.cast_natCast]
    exact h
  exact hm (Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd (m : ℤ)).1 h'))

lemma zv_pow_nat (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) {n : ℕ} (hn : n ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ n - 1) =
      emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + padicValNat ℓ n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.out.ne_one
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hy1 : (ℓ : ℤ_[ℓ]) ∣ x ^ ℓ ^ e - 1 := hx.trans (sub_one_dvd_pow_sub_one x _)
  have h1 := emultiplicity_pow_sub_pow_of_prime zv_prime hy1
    (zv_not_dvd_of_dvd_sub_one (by simpa using hy1)) (zv_not_dvd_cast hm)
  rw [one_pow] at h1
  have hv : padicValNat ℓ (ℓ ^ e * m) = e := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hℓ.out.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  rw [pow_mul, h1, zv_pow_prime_pow x hx h2 e, hv]

end ZpowValAux

theorem valuation_zpow_sub_one : ZpowVal := by
  intro ℓ _ u s hs1 hs2 hval j hj

  have key : ∀ y : ℤ_[ℓ]ˣ, emultiplicity (ℓ : ℤ_[ℓ]) ((y : ℤ_[ℓ]) - 1) = s → ∀ n : ℕ, n ≠ 0 →
      ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValNat ℓ n := by
    intro y hy n hn
    have hy1 : (ℓ : ℤ_[ℓ]) ∣ (y : ℤ_[ℓ]) - 1 := by
      have h1 := pow_dvd_of_le_emultiplicity (k := 1) (by rw [hy]; exact_mod_cast hs1)
      rwa [pow_one] at h1
    have hy2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ (y : ℤ_[ℓ]) - 1 := fun h =>
      pow_dvd_of_le_emultiplicity (by rw [hy]; exact_mod_cast hs2 h)
    have he := zv_pow_nat (y : ℤ_[ℓ]) hy1 hy2 hn
    rw [← Units.val_pow_eq_pow_val, hy] at he
    have hne : ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at he
      exact absurd he (by norm_cast)
    refine ⟨hne, ?_⟩
    rw [zv_emult_eq_val hne] at he
    exact_mod_cast he
  have hx0 : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hval
    omega
  have hem : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = s := by
    rw [zv_emult_eq_val hx0, hval]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj rfl
    rw [zpow_natCast, padicValInt.of_nat]
    simpa only [Nat.padicValNat_def] using key u hem n hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj (by simp)
    have hinv : emultiplicity (ℓ : ℤ_[ℓ]) (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s := by
      have e : ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = (-((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((u : ℤ_[ℓ]) - 1) := by
        rw [mul_sub, neg_mul, Units.inv_mul]
        ring
      rw [e, zv_emult_unit_mul (Units.isUnit _).neg, hem]
    have hv : padicValInt ℓ (-(n : ℤ)) = padicValNat ℓ n := by
      simp [padicValInt, Nat.padicValNat_def]
    rw [zpow_neg, zpow_natCast, ← inv_pow, hv]
    exact key u⁻¹ hinv n hn

end Formalism.WindowSums
end

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.ValProd
namespace Formalism.WindowSums

open Finset

section ValProdAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma vp_val_neg (x : ℤ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 : (-1 : ℤ_[ℓ]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm1 : (-1 : ℤ_[ℓ]).valuation = 0 := by
    have h := PadicInt.valuation_mul h1 h1
    rw [neg_one_mul, neg_neg, PadicInt.valuation_one] at h
    omega
  rw [← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]

lemma vp_val_prod {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ_[ℓ])
    (h : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) ≠ 0 ∧ (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [PadicInt.valuation_one]
  · intro a S ha ih h
    have hS : ∀ i ∈ S, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := h a (Finset.mem_insert_self a S)
    obtain ⟨h1, h2⟩ := ih hS
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, by rw [PadicInt.valuation_mul ha0 h1, h2]⟩

private theorem prime_pow_ne_zero_and_valuation_eq (n : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ n ≠ 0 ∧ ((ℓ : ℤ_[ℓ]) ^ n).valuation = n := by
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by
    intro h
    have h' := PadicInt.valuation_p (p := ℓ)
    rw [h, PadicInt.valuation_zero] at h'
    exact absurd h' (by norm_num)
  induction n with
  | zero => simp [PadicInt.valuation_one]
  | succ n ih =>
    refine ⟨pow_ne_zero _ hℓ0, ?_⟩
    rw [pow_succ, PadicInt.valuation_mul ih.1 hℓ0, ih.2, PadicInt.valuation_p]

lemma vp_sum_padicValNat (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by
  induction M with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]
    omega

end ValProdAux

theorem valProd_of (hZ : ZpowVal) : ValProd := by
  unfold ValProd
  unfold ZpowVal at hZ
  intro ℓ hp u s hs h2 hv
  have key : ∀ j : ℤ, j ≠ 0 →
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
    intro j hj
    obtain ⟨h1, h2'⟩ := hZ ℓ u s hs h2 hv j hj
    rw [← neg_sub, vp_val_neg, h2']
    exact ⟨neg_ne_zero.mpr h1, rfl⟩
  refine ⟨fun M => ?_, fun J hJ => ?_⟩
  · have hf : ∀ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) ≠ 0 ∧
        (1 - (u : ℤ_[ℓ]) ^ i).valuation = s + padicValNat ℓ i := by
      intro i hi
      have hi0 : (i : ℤ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hk := key i hi0
      have e : ((u ^ (i : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ i := by
        rw [zpow_natCast, Units.val_pow_eq_pow_val]
      have hv' : padicValInt ℓ (i : ℤ) = padicValNat ℓ i := by
        rw [padicValInt.of_nat, Nat.padicValNat_def]
      rw [e, hv'] at hk
      exact hk
    obtain ⟨h1, h2'⟩ := vp_val_prod (Finset.Icc 1 M)
      (fun i => 1 - (u : ℤ_[ℓ]) ^ i) (fun i hi => (hf i hi).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun i hi => (hf i hi).2), Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, smul_eq_mul,
      vp_sum_padicValNat, Nat.add_sub_cancel]
  · have hf : ∀ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
        (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
      intro j hj
      have hj0 : -j ≠ 0 := neg_ne_zero.mpr (fun h => hJ (by rw [← h]; exact hj))
      obtain ⟨h1, h2'⟩ := key (-j) hj0
      refine ⟨h1, h2'.trans ?_⟩
      simp [padicValInt]
    obtain ⟨h1, h2'⟩ := vp_val_prod J
      (fun j => 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun j hj => (hf j hj).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun j hj => (hf j hj).2), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul]

theorem killerVal_of (hZ : ZpowVal) : KillerVal := by
  unfold KillerVal
  unfold ZpowVal at hZ
  intro ℓ hp h2 c hc e JJ
  have h22 : ℓ = 2 → 2 ≤ 1 := fun h => absurd h h2
  have hf : ∀ i ∈ JJ.erase 0,
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = 1 + e + padicValInt ℓ i := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hp0 : ((ℓ : ℤ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hj : i * (ℓ : ℤ) ^ e ≠ 0 := mul_ne_zero hi0 hp0
    obtain ⟨h1, h2'⟩ := hZ ℓ c 1 le_rfl h22 hc _ hj
    rw [← neg_sub, vp_val_neg, h2', padicValInt.mul hi0 hp0]
    refine ⟨neg_ne_zero.mpr h1, ?_⟩
    have hpe : padicValInt ℓ ((ℓ : ℤ) ^ e) = e := by
      simp [padicValInt, Int.natAbs_pow]
    omega
  obtain ⟨h1, h2'⟩ := vp_val_prod (JJ.erase 0)
    (fun i => 1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun i hi => (hf i hi).1)
  obtain ⟨hP1, hP2⟩ := prime_pow_ne_zero_and_valuation_eq (ℓ := ℓ) e
  have hev : (PP ℓ c e JJ).eval 1 =
      (∏ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * (ℓ : ℤ_[ℓ]) ^ e := by
    simp [PP, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [hev]
  refine ⟨mul_ne_zero h1 hP1, ?_⟩
  rw [PadicInt.valuation_mul h1 hP1, hP2, h2', Finset.sum_congr rfl (fun i hi => (hf i hi).2)]

end Formalism.WindowSums
end

section -- merged from Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms
noncomputable section

namespace Formalism.WindowSums

open PowerSeries

theorem mem_span_iff_of_distinct_exponents : DistinctTerms := by
  intro O _ _ ϖ hϖ hnu ι I w e m B s hw he
  classical
  constructor
  · intro hmem
    by_contra hbad
    push_neg at hbad
    obtain ⟨i₁, hi₁, hb₁, hs₁⟩ := hbad
    have hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩
    obtain ⟨i₀, hi₀J, hmin⟩ := (I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne
    obtain ⟨hi₀, hB, hs⟩ := Finset.mem_filter.mp hi₀J
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hcoef := congrArg (PowerSeries.coeff (e i₀)) hab
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_mul_C, map_sum] at hcoef
    have hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) =
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      intro i _
      rw [PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl,
      Nat.sub_self] at hcoef
    have hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀,
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      refine Finset.dvd_sum fun i hi => ?_
      obtain ⟨hne, hiI⟩ := Finset.mem_erase.mp hi
      by_cases hle : e i ≤ e i₀
      · rw [if_pos hle]
        have hlt : e i < e i₀ := lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)
        have hms : s ≤ m i := by
          by_contra hms
          push_neg at hms
          have := hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _
      · rw [if_neg hle, zero_mul]
        exact dvd_zero _
    have hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ := by
      have h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ =
          PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀,
            (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
        rw [hcoef]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_left _ _) hrest
    have hu : IsUnit (PowerSeries.coeff 0 (w i₀)) := by
      have := (hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))
      simpa using this
    have hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hs.le]
    rw [hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))] at hdvd
    have hd2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd
    have hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀) :=
      (dvd_pow_self ϖ (by omega)).trans hd2
    exact hnu (isUnit_of_dvd_unit hd3 hu)
  · intro h
    refine Ideal.sum_mem _ fun i hi => ?_
    rcases h i hi with hb | hs
    · have hx : (X : PowerSeries O) ^ B ∈
          Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i)) := by
        rw [show e i = B + (e i - B) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hx
    · have hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s))) := by
        rw [show m i = s + (m i - s) by omega, pow_add, map_mul]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hc

end Formalism.WindowSums
end
end
