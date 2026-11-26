module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsPowerMulUnitNorm
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FrobFixNegOne
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section General

variable {R : Type*} [CommRing R] (p : ℕ)

def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x

variable {p}

theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2

theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  · have h := frobFix_iter h1 (f2 - 1)
    rwa [Nat.sub_add_cancel hf2] at h
  · have h := frobFix_iter h2 (f1 - 1)
    rwa [Nat.sub_add_cancel hf1, mul_comm] at h

theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p (x * y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

private theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h

theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p (x + y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have h3 := frobFix_add_lemma hp x y f
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add h3 h1) h2

theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  refine ⟨1, one_pos, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  · rw [pow_one, hodd.neg_one_pow, sub_self]
    exact dvd_zero _

theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p (-x) := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx

theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩

theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩

theorem frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have htot : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, htot, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _

end General

variable (l : ℕ) [Fact l.Prime]

theorem rmu_frob (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f : ℕ, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Subring.closure (muP l)), FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln (Subtype.ext (by simpa using hzn))
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  refine ⟨f, hf, r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_norm_le {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact (muP_norm l hx).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem kmu_frac {x : ℂ_[l]} (hx : x ∈ Kmu l) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, b ≠ 0 ∧ x = a / b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  by_cases hz0 : z = 0
  · refine ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, one_ne_zero, ?_⟩
    rw [hz0, div_zero, zero_div]
  · exact ⟨y, hy, z, hz, hz0, rfl⟩

theorem exists_power_mul_unitNorm (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  induction k with
  | zero =>
    intro a ha _ h
    rw [pow_zero, one_mul] at h
    exact absurd (rmu_norm_le l ha) (not_le.2 h)
  | succ k ih =>
    intro a ha ha0 h
    rcases (rmu_norm_le l ha).eq_or_lt with h1 | h1
    · exact ⟨0, a, ha, 1, (Rmu l).one_mem, h1, norm_one, by rw [pow_zero, one_mul, mul_one]⟩
    obtain ⟨f, hf, r, hr, he⟩ := rmu_frob l a ha
    have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
    have hq : 1 ≤ l ^ f - 1 := by
      have : 2 ≤ l ^ f := le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow hf.ne' l)
      omega
    set u := a ^ (l ^ f - 1) - 1 with hu
    have huR : u ∈ Rmu l := sub_mem (pow_mem ha _) (Rmu l).one_mem
    have hu1 : ‖u‖ = 1 := by
      have hsm : ‖a ^ (l ^ f - 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) h1 (by omega)
      have := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_eq_of_norm_sub_lt' l (a := u) (b := -1)
        (by rw [hu, sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one]; exact hsm)
      rwa [norm_neg, norm_one] at this
    have hau : a * u = (l : ℂ_[l]) * r := by
      rw [← he, hu, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l ^ f)]
    have hnr : ‖r‖ = l * ‖a‖ := by
      have := congrArg norm hau
      rw [norm_mul, norm_mul, hu1, mul_one, norm_l_Cl] at this
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      rw [this, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hnr
      have : (0 : ℝ) < l * ‖a‖ := mul_pos (by positivity) (norm_pos_iff.2 ha0)
      linarith
    have h' : 1 < (l : ℝ) ^ k * ‖r‖ := by
      rw [hnr, ← mul_assoc, ← pow_succ]; exact h
    obtain ⟨m, c, hc, v, hv, hc1, hv1, hrv⟩ := ih r hr hr0 h'
    refine ⟨m + 1, c, hc, u * v, mul_mem huR hv, hc1, by rw [norm_mul, hu1, hv1, one_mul], ?_⟩
    rw [← mul_assoc, hau, mul_assoc, hrv, pow_succ]
    ring

theorem rmu_shape {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖a‖⁻¹) (by exact_mod_cast (Fact.out : l.Prime).one_lt :
    (1 : ℝ) < l)
  refine exists_power_mul_unitNorm l k a ha ha0 ?_
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  calc (1 : ℝ) = ‖a‖⁻¹ * ‖a‖ := (inv_mul_cancel₀ hpos.ne').symm
    _ < (l : ℝ) ^ k * ‖a‖ := mul_lt_mul_of_pos_right hk hpos

theorem kmu_shape {x : ℂ_[l]} (hx : x ∈ Kmu l) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ x = (l : ℂ_[l]) ^ m * (a / b) := by
  obtain ⟨a, ha, b, hb, hb0, rfl⟩ := kmu_frac l hx
  have ha0 : a ≠ 0 := by rintro rfl; exact hx0 (zero_div b)
  obtain ⟨m, c, hc, u, hu, hc1, hu1, hau⟩ := rmu_shape l ha ha0
  obtain ⟨n, d, hd, v, hv, hd1, hv1, hbv⟩ := rmu_shape l hb hb0
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd1
  refine ⟨(m : ℤ) - n, c * v, mul_mem hc hv, d * u, mul_mem hd hu,
    by rw [norm_mul, hc1, hv1, one_mul], by rw [norm_mul, hd1, hu1, one_mul], ?_⟩
  rw [zpow_sub₀ hl0, zpow_natCast, zpow_natCast]
  have ha' : a = (l : ℂ_[l]) ^ m * c / u := by rw [← hau, mul_div_cancel_right₀ _ hu0]
  have hb' : b = (l : ℂ_[l]) ^ n * d / v := by rw [← hbv, mul_div_cancel_right₀ _ hv0]
  rw [ha', hb']
  field_simp

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_le_kmu {x : ℂ_[l]} (hx : x ∈ Rmu l) : x ∈ Kmu l := by
  have h : Rmu l ≤ (Kmu l).toSubring := by
    rw [Rmu, Subring.closure_le]
    intro z hz
    exact Subfield.subset_closure hz
  exact h hx

theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  · exact (MaximalUnramifiedExtension l).zero_mem
  · exact kmu_le_kur l (Subfield.subset_closure h)

theorem norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h
  exact h

theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h1
    rw [max_eq_right hlt.le] at h
    have h2 : max ‖x‖ ‖x - y‖ < ‖y‖ := max_lt hlt h
    linarith
  · have h1 := norm_sub_le_max_padic l y (y - x)
    rw [sub_sub_cancel] at h1
    rw [max_eq_left hgt.le, norm_sub_rev] at h
    have h2 : max ‖y‖ ‖y - x‖ < ‖x‖ := max_lt hgt h
    linarith

private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  have e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [e] at h
  exact h

theorem norm_prime_pos_complexPadic : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)

theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)

theorem kmu_discrete {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1 ⊢
  have hm : 1 ≤ m := by
    by_contra hc
    have hm0 : m ≤ 0 := by omega
    have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
    linarith
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm
    _ = ‖(l : ℂ_[l])‖ := zpow_one _

theorem exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem kmu_rep {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact ⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨m, a, ha', b, hb', ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · have := one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
    · exact h
    · have := zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
  subst hm
  obtain ⟨α, hα, hαa⟩ := exists_teichmuller_rep_mod_prime l ha'
  obtain ⟨β, hβ, hβb⟩ := exists_teichmuller_rep_mod_prime l hb'
  have hβ1 : ‖β‖ = 1 := by
    have h2 : ‖b - β‖ < max ‖b‖ ‖β‖ :=
      lt_of_le_of_lt hβb (lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) (hb ▸ le_max_left _ _))
    rw [← norm_eq_of_norm_sub_lt_max l h2, hb]
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hβ0 : β ≠ 0 := by intro h; rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1
  refine ⟨α * β⁻¹, tch_mul l hα (tch_inv l hβ), ?_⟩
  have he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹
      = ((a - α) * β - α * (b - β)) / (b * β) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]
  refine (norm_sub_le_max_padic l _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, hβ1, mul_one]; exact hαa
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (tch_norm_le l hα)).trans hβb

theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  have hc : x ∈ closure ((Kmu l : Set ℂ_[l])) := hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hc e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

theorem kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ hpos
  have heq : ‖x‖ = ‖y‖ := norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))
  rw [heq] at h1 ⊢
  exact kmu_discrete l hy h1

theorem kur_rep {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)
  have hl1 := norm_prime_lt_one_complexPadic l
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h
    exact h.trans (max_le h1 (by linarith))
  obtain ⟨ξ, hξ, hyξ⟩ := kmu_rep l hy hy1
  refine ⟨ξ, hξ, ?_⟩
  have h := norm_sub_le_max_padic l (x - y) (ξ - y)
  rw [sub_sub_sub_cancel_right, norm_sub_rev ξ y] at h
  exact h.trans (max_le hxy.le hyξ)

end ReciprocityTheory.ChartRestriction.L1
