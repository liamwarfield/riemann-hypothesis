module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SgDistribution
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.Distr

open Filter Topology Finset

def E (q u : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ n * u)

def T (q u : ℂ) : ℂ := E q u * E q (q * u⁻¹)

lemma summ {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Summable fun n : ℕ => ‖-(q ^ n * u)‖ := by
  simp only [norm_neg, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _

lemma mult {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun n : ℕ => (1 - q ^ n * u) := by
  simp only [sub_eq_add_neg]
  exact multipliable_one_add_of_summable (summ hq u)

lemma E_ne {q : ℂ} (hq : ‖q‖ < 1) {u : ℂ} (h : ∀ n : ℕ, q ^ n * u ≠ 1) : E q u ≠ 0 := by
  unfold E
  simp only [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (fun n => ?_) (summ hq u)
  rw [← sub_eq_add_neg]
  exact sub_ne_zero.mpr (h n).symm

lemma E_tend {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) :
    Tendsto (fun N => ∏ n ∈ range N, (1 - q ^ n * u)) atTop (𝓝 (E q u)) :=
  (mult hq u).hasProd.tendsto_prod_nat

lemma E_step {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : E q u = (1 - u) * E q (q * u) := by
  have h1 := (E_tend hq u).comp (tendsto_add_atTop_nat 1)
  have h2 := (E_tend hq (q * u)).const_mul (1 - u)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp, prod_range_succ', pow_zero, one_mul, pow_succ, mul_assoc]
  ring

lemma E_split {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) (u : ℂ) :
    ∏ j ∈ range m, E (q ^ m) (q ^ j * u) = E q u := by
  have hqm : ‖q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hm.ne'
  have h1 := (E_tend hq u).comp (tendsto_id.const_mul_atTop' hm)
  have h2 := tendsto_finsetProd (range m) fun j _ => E_tend hqm (q ^ j * u)
  refine tendsto_nhds_unique (h2.congr fun N => ?_) h1
  simp only [Function.comp, id]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, prod_range_add, ← ih, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [prod_range_succ, ← pow_mul, pow_add, mul_assoc]

lemma T_step {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    T q u = (-u) * T q (q * u) := by
  unfold T
  have : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  rw [this, E_step hq u, E_step hq u⁻¹]
  field_simp
  ring

lemma T_steps {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) (k : ℕ) :
    T q u = (-u) ^ k * q ^ (k.choose 2) * T q (q ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, T_step hq h0 (mul_ne_zero (pow_ne_zero k h0) hu), Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [← mul_assoc q, ← pow_succ']
    ring

lemma T_split {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {m : ℕ} (hm : 0 < m) {u : ℂ} (hu : u ≠ 0) :
    ∏ j ∈ range m, T (q ^ m) (q ^ j * u) = T q u := by
  unfold T
  rw [prod_mul_distrib, E_split hq hm, ← E_split hq hm (q * u⁻¹), ← prod_range_reflect _ m]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  congr 1
  have : q ^ m = q ^ (m - 1 - j) * q ^ j * q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [this]
  field_simp

lemma cth_eq {q : ℂ} (hq : ‖q‖ < 1) (c : ℕ) {t : ℂ} (h : ∀ n : ℕ, q ^ n * t ^ c ≠ 1)
    (h' : ∀ n : ℕ, q ^ n * (q * (t ^ c)⁻¹) ≠ 1) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * T q t ^ (c ^ 2) / T q (t ^ c) := by
  have h1 : E q (q * t ^ c) ≠ 0 := E_ne hq fun n => by
    rw [← mul_assoc, ← pow_succ]; exact h _
  have h2 : E q (q * (t ^ c)⁻¹) ≠ 0 := E_ne hq h'
  have hp : HasProd (fun m : ℕ => cthFac c q t (m + 1))
      (E q (q * t) ^ (c ^ 2) * E q (q * t⁻¹) ^ (c ^ 2) / (E q (q * t ^ c) * E q (q * (t ^ c)⁻¹))) := by
    have a := (((mult hq (q * t)).hasProd.pow (c ^ 2)).mul ((mult hq (q * t⁻¹)).hasProd.pow (c ^ 2)))
    have b := ((mult hq (q * t ^ c)).hasProd.mul (mult hq (q * (t ^ c)⁻¹)).hasProd)
    have := Tendsto.div a b (mul_ne_zero h1 h2)
    unfold HasProd
    refine this.congr fun s => ?_
    simp only [Pi.div_apply, cthFac, prod_div_distrib, pow_succ, mul_assoc]
  unfold cth T
  rw [hp.tprod_eq, E_step hq t, E_step hq (t ^ c)]
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  ring

lemma image_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) :
    (range m).image (fun j => c * j % m) = range m ∧ Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
  have hi : Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
    intro a ha b hb hab
    have h1 : a ≡ b [MOD m] := Nat.ModEq.cancel_left_of_coprime h.symm hab
    exact Nat.ModEq.eq_of_lt_of_lt h1 (by simpa using ha) (by simpa using hb)
  refine ⟨eq_of_subset_of_card_le (fun x hx => ?_) (by rw [card_image_of_injOn hi]), hi⟩
  obtain ⟨j, -, rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (Nat.mod_lt _ hm)

lemma prod_mod {M : Type*} [CommMonoid M] {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → M) :
    ∏ j ∈ range m, f (c * j % m) = ∏ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, prod_image h2]

lemma sum_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → ℤ) :
    ∑ j ∈ range m, f (c * j % m) = ∑ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, sum_image h2]

lemma two_choose (k : ℕ) : 2 * (k.choose 2 : ℤ) = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    push_cast
    linear_combination ih

lemma sum_one (m : ℕ) : 2 * ∑ j ∈ range m, (j : ℤ) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma sum_two (m : ℕ) : 6 * ∑ j ∈ range m, (j : ℤ) ^ 2 = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma divmod (c m j : ℕ) : (c : ℤ) * j = m * ((c * j / m : ℕ) : ℤ) + ((c * j % m : ℕ) : ℤ) := by
  exact_mod_cast (Nat.div_add_mod (c * j) m).symm

lemma smoothedTheta_distribution_t_exponent_eq {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {b : ℤ} (hb : 2 * b = c - c ^ 2) :
    m * b + c * ((∑ j ∈ range m, c * j / m : ℕ) : ℤ) = b := by
  have h1 : m * ∑ j ∈ range m, ((c * j / m : ℕ) : ℤ) = (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    rw [sub_mul, one_mul, mul_sum, mul_sum]
    conv_rhs => rw [← sum_mod hm h (fun j => (j : ℤ)), ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by linear_combination -divmod c m j
  have hm' : (2 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  rw [Nat.cast_sum]
  linear_combination (2 * c) * h1 + (c * (c - 1)) * sum_one m + (m * (m - 1)) * hb

lemma expo_q {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {a b : ℤ} (ha : 12 * a = c ^ 2 - 1) (hb : 2 * b = c - c ^ 2) :
    m * a * m + (∑ j ∈ range m, (j : ℤ)) * b +
      ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) = a := by
  have h1 : 2 * m * ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) =
      (c ^ 2 - 1) * ∑ j ∈ range m, (j : ℤ) ^ 2 - m * (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    have e : ∀ S₁ S₂ : ℤ, (c ^ 2 - 1) * S₂ - m * (c - 1) * S₁ = c ^ 2 * S₂ - m * c * S₁ - (S₂ - m * S₁) := by
      intros; ring
    rw [e, Nat.cast_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
      ← sum_mod hm h (fun j => (j : ℤ) ^ 2 - m * j), ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have h2 := divmod c m j
    have h3 := two_choose (c * j / m)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul m]
    generalize ((c * j / m).choose 2 : ℤ) = C at *
    generalize ((c * j / m : ℕ) : ℤ) = k at *
    generalize ((c * j % m : ℕ) : ℤ) = r at *
    linear_combination m ^ 2 * h3 - (c * j + m * k + r - m) * h2
  have hm' : (12 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  linear_combination 6 * h1 + (c ^ 2 - 1) * sum_two m + (6 * m * b - 3 * m * (c - 1)) * sum_one m
    + (m ^ 3 - m) * ha + 3 * m ^ 2 * (m - 1) * hb

theorem _root_.GlobalTheory.Sieg.prod_cth_mul_pow : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  intro c m Q t hc h6 hm hcm hQ h0 ht hn
  have hqm : ‖Q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hQ hm.ne'
  have hs : t ^ c ≠ 0 := pow_ne_zero _ ht
  have hodd : Odd c := (Nat.coprime_two_right).mp (h6.coprime_dvd_right (by norm_num))
  have hinv : ∀ n : ℤ, Q ^ n * (t ^ c)⁻¹ ≠ 1 := fun n hh => by
    apply hn (-n)
    rw [← inv_inj, mul_inv, ← zpow_neg, neg_neg, hh, inv_one]
  have h12 : 12 ∣ c ^ 2 - 1 := by
    have h2 : c % 2 = 1 := Nat.odd_iff.mp hodd
    have h3 : ¬ 3 ∣ c := fun hd => by
      have := Nat.dvd_gcd hd (show 3 ∣ 6 by norm_num)
      rw [h6] at this; omega
    have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
    have h4 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
    omega
  obtain ⟨a, ha⟩ := h12
  have ha' : 12 * (a : ℤ) = c ^ 2 - 1 := by
    have : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : c ^ 2 = 12 * a + 1 := by omega
    have h3 : (c : ℤ) ^ 2 = 12 * a + 1 := by exact_mod_cast h2
    linarith
  have haa : (c ^ 2 - 1) / 12 = a := by omega
  obtain ⟨b, hb⟩ : ∃ b : ℤ, 2 * b = c - c ^ 2 := by
    obtain ⟨d, hd⟩ := hodd
    exact ⟨-(c * d), by rw [hd]; push_cast; ring⟩
  have hbb : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = b := by omega
  have hL : ∀ j ∈ range m, cth c (Q ^ m) (t * Q ^ j) =
      (Q ^ m) ^ a * ((-t) ^ b * (Q ^ j) ^ b) * T (Q ^ m) (Q ^ j * t) ^ (c ^ 2) / T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    intro j _
    rw [cth_eq hqm c, haa, hbb, ← neg_mul, mul_zpow, mul_pow t, ← pow_mul Q j, mul_comm t, mul_comm (t ^ c),
      mul_comm j c]
    · intro n hh
      apply hn ((m * n + j * c : ℕ) : ℤ)
      rw [← hh, zpow_natCast]; ring
    · intro n hh
      apply hinv ((m * n + m : ℕ) - (j * c : ℕ) : ℤ)
      rw [← hh, zpow_sub₀ h0, zpow_natCast, zpow_natCast]; field_simp; ring
  have hD : T Q (t ^ c) = (-t) ^ (c * ∑ j ∈ range m, c * j / m) *
      Q ^ (∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2)) *
      ∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    rw [← T_split hQ h0 hm hs, ← prod_mod hm hcm (fun j => T (Q ^ m) (Q ^ j * t ^ c)), mul_sum,
      ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [T_steps hqm (pow_ne_zero _ h0) (mul_ne_zero (pow_ne_zero _ h0) hs) (c * j / m), ← mul_assoc, ← pow_mul,
      ← pow_mul, ← pow_add, Nat.div_add_mod, pow_mul (-t), hodd.neg_pow, ← mul_neg, mul_pow, ← pow_mul, pow_add]
    ring
  rw [prod_congr rfl hL, cth_eq hQ c (fun n => by simpa using hn n)
    (fun n => by rw [← mul_assoc, ← pow_succ, ← zpow_natCast]; exact hinv _), haa, hbb, hD, prod_div_distrib,
    prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, prod_pow, T_split hQ h0 hm ht, card_range,
    prod_zpow, prod_pow_eq_pow_sum]
  have e1 := congrArg (fun z : ℤ => (-t) ^ z) (smoothedTheta_distribution_t_exponent_eq hm hcm hb)
  have e2 := congrArg (fun z : ℤ => Q ^ z) (expo_q hm hcm ha' hb)
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  rw [mul_comm (m : ℤ) b, ← Nat.cast_mul c] at e1
  rw [← Nat.cast_sum] at e2
  simp only [zpow_add₀ hnt, zpow_add₀ h0, zpow_natCast, zpow_mul] at e1 e2
  conv_rhs => rw [← e1, ← e2]
  generalize (∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c)) = P
  by_cases hP : P = 0
  · simp [hP]
  field_simp

end GlobalTheory.Sieg.Distr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistributionStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_smoothedThetaQProduct_distribution : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_pow | exact GlobalTheory.Sieg.prod_cth_mul_pow | (intros; apply GlobalTheory.Sieg.prod_cth_mul_pow <;> assumption)
end
end

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.SiegDist

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_int_mul (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_int_mul]; ring_nf

lemma ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; ring_nf

lemma ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, ← Real.exp_zero, Real.exp_lt_exp]
  have := mul_pos Real.pi_pos τ.im_pos
  linarith

lemma ee_eq_one (u v : ℚ) (τ : ℍ) (h : ee ((u : ℂ) * τ + v) = 1) : u = 0 ∧ ∃ k : ℤ, v = k := by
  unfold ee at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (u : ℂ) * τ + v = k := by
    apply mul_left_cancel₀ hne
    rw [hk]; ring
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hu : u = 0 := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hu
  simp at hre
  exact ⟨rfl, k, by exact_mod_cast hre⟩

theorem sg_distribution : ∀ (c m : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ = sg c x τ := by
  intro c m x τ hA hm hcm
  obtain ⟨hc1, hc6, hnot⟩ := hA
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : ee (τ : ℂ) ≠ 0 := ee_ne_zero _
  have hsplit : ∀ a b : ℕ, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = cth c (ee (τ : ℂ)) (ee ((((x 0 : ℂ) + a) * τ + x 1) / m) * ee ((b : ℂ) / m)) := by
    intro a b
    unfold sg
    rw [← ee_add]
    congr 2
    simp [pt]
    field_simp
    ring
  have hpow : ∀ a : ℕ, ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ m = ee (pt x τ) * ee (τ : ℂ) ^ a := by
    intro a
    rw [← ee_nat_mul, ← ee_nat_mul, ← ee_add]
    congr 1
    simp only [pt]
    field_simp
    ring
  have hND : ∀ n : ℤ, ee (τ : ℂ) ^ n * ee (pt x τ) ^ c ≠ 1 := by
    intro n h
    have h' : ee ((((n : ℚ) + c * x 0 : ℚ) : ℂ) * τ + ((c * x 1 : ℚ) : ℂ)) = 1 := by
      rw [← h, ← ee_int_mul, ← ee_nat_mul, ← ee_add]
      congr 1; simp only [pt]; push_cast; ring
    obtain ⟨h0, k, hk⟩ := ee_eq_one _ _ τ h'
    apply hnot
    refine ⟨⟨-n, ?_⟩, ⟨k, hk.symm⟩⟩
    push_cast; linarith
  have hD1 : ∀ a : ℕ, ∀ n : ℤ, ee (τ : ℂ) ^ n * ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ (c * m) ≠ 1 := by
    intro a n h
    rw [mul_comm c m, pow_mul, hpow a, mul_pow, ← pow_mul] at h
    apply hND (n + ((a * c : ℕ) : ℤ))
    rw [zpow_add₀ hq0, zpow_natCast, ← h]
    ring
  calc ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = ∏ a ∈ Finset.range m, cth c (ee (τ : ℂ) ^ m) (ee (pt x τ) * ee (τ : ℂ) ^ a) := by
        apply Finset.prod_congr rfl
        intro a _
        simp_rw [hsplit a]
        rw [GlobalTheory.T.smoothedThetaQProduct_distribution_relation c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) (hD1 a), hpow a]
    _ = cth c (ee (τ : ℂ)) (ee (pt x τ)) :=
        GlobalTheory.T.prod_smoothedThetaQProduct_distribution c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) hND
    _ = sg c x τ := rfl

end GlobalTheory.SiegDist
end
end

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simpa only [Finset.prod_apply, sgC] using
    GlobalTheory.SiegDist.sg_distribution c m x (UpperHalfPlane.ofComplex z) hA hm hcm

end GlobalTheory.KZDist
