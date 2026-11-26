module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumChar
theorem UpperTheory.Reformulated.B.Qe46.sum_char :
    ∀ {G : Type} [inst : CommGroup G] [inst_1 : Fintype G] (χ : G →* ℂˣ),
    χ ≠ (1 : G →* ℂˣ) → ∑ z : G, (↑((χ : G → ℂˣ) z) : ℂ) = (0 : ℂ) := by
  intro G _ _ χ hχ
  have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext z
    have hz := DFunLike.congr_fun h z
    simpa using hz
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinFld
section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinChar
open Finset ComplexConjugate

namespace UpperTheory.Zero.LLC.CharacterSumPairs

variable {G : Type} [CommGroup G] [Fintype G]

theorem norm_char (χ : G →* ℂˣ) (z : G) : ‖((χ z : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ z : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

theorem sum_char (χ : G →* ℂˣ) (h : χ ≠ 1) : ∑ z, ((χ z : ℂˣ) : ℂ) = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe46.sum_char χ h

theorem conj_char (χ : G →* ℂˣ) (z : G) : conj ((χ z : ℂˣ) : ℂ) = (((χ⁻¹) z : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_char χ z)]

open Classical in
theorem sum_mul_conj (χ ψ : G →* ℂˣ) :
    ∑ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  have : ∀ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = (((χ * ψ⁻¹) z : ℂˣ) : ℂ) := by
    intro z
    rw [conj_char, MonoidHom.mul_apply, Units.val_mul]
  simp_rw [this]
  split_ifs with h
  · subst h
    simp
  · exact sum_char _ (fun hh => h (mul_inv_eq_one.mp hh))

noncomputable def dif (A B : Finset (G →* ℂˣ)) (z : G) : ℂ :=
  ∑ χ ∈ A, ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, ((χ z : ℂˣ) : ℂ)

open Classical in
theorem inner_dif (A B : Finset (G →* ℂˣ)) (ψ : G →* ℂˣ) :
    ∑ z, dif A B z * conj ((ψ z : ℂˣ) : ℂ) =
      (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0)) := by
  have key : ∀ C : Finset (G →* ℂˣ),
      ∑ z, (∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)) * conj ((ψ z : ℂˣ) : ℂ) =
        (Fintype.card G : ℂ) * (if ψ ∈ C then 1 else 0) := by
    intro C
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [sum_mul_conj]
    rw [Finset.sum_ite_eq' C ψ]
    split_ifs <;> simp
  simp only [dif, sub_mul, Finset.sum_sub_distrib, key]
  ring

theorem parseval (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) :
    ∑ z, dif A B z * conj (dif A B z) = (Fintype.card G : ℂ) * ((#A : ℂ) + #B) := by
  classical
  have hc : ∀ z, conj (dif A B z) =
      ∑ χ ∈ A, conj ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, conj ((χ z : ℂˣ) : ℂ) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dif, map_sub, map_sum]
  simp_rw [hc, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.univ) (t := B)]
  simp_rw [inner_dif]
  have hA : ∑ ψ ∈ A, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = (Fintype.card G : ℂ) * #A := by
    rw [Finset.sum_congr rfl (g := fun _ => (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ B := Finset.disjoint_left.mp hd hψ
      simp [hψ, this]
  have hB : ∑ ψ ∈ B, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = - ((Fintype.card G : ℂ) * #B) := by
    rw [Finset.sum_congr rfl (g := fun _ => - (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ A := Finset.disjoint_right.mp hd hψ
      simp [hψ, this]
  rw [hA, hB]
  ring

theorem norm_dif_le (A B : Finset (G →* ℂˣ)) (z : G) : ‖dif A B z‖ ≤ (#A : ℝ) + #B := by
  have h : ∀ C : Finset (G →* ℂˣ), ‖∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)‖ ≤ #C := by
    intro C
    refine (norm_sum_le _ _).trans ?_
    simp [norm_char]
  exact (norm_sub_le _ _).trans (add_le_add (h A) (h B))

theorem card_le (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → dif A B z = 0) (hne : 0 < #A + #B) :
    Fintype.card G ≤ #D * (#A + #B) := by
  have h1 : ∑ z, ‖dif A B z‖ ^ 2 = (Fintype.card G : ℝ) * ((#A : ℝ) + #B) := by
    have := parseval A B hd
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  have h2 : ∑ z, ‖dif A B z‖ ^ 2 = ∑ z ∈ D, ‖dif A B z‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
    simp [hD z hz]
  have h3 : ∑ z ∈ D, ‖dif A B z‖ ^ 2 ≤ (#D : ℝ) * ((#A : ℝ) + #B) ^ 2 := by
    have : ∀ z ∈ D, ‖dif A B z‖ ^ 2 ≤ ((#A : ℝ) + #B) ^ 2 := fun z _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_dif_le A B z) 2
    simpa using Finset.sum_le_sum this
  have hpos : (0 : ℝ) < (#A : ℝ) + #B := by exact_mod_cast hne
  have h4 : (Fintype.card G : ℝ) ≤ (#D : ℝ) * ((#A : ℝ) + #B) := by
    have : (Fintype.card G : ℝ) * ((#A : ℝ) + #B) ≤ ((#D : ℝ) * ((#A : ℝ) + #B)) * ((#A : ℝ) + #B) := by
      rw [← h1, h2]
      nlinarith [h3]
    exact le_of_mul_le_mul_right this hpos
  exact_mod_cast h4

theorem mul_mem (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → dif A B z = 0) (η : G →* ℂˣ) (hη : ∀ z ∈ D, η z = 1) (ψ : G →* ℂˣ) :
    (ψ ∈ A → ψ * η ∈ A) ∧ (ψ ∈ B → ψ * η ∈ B) := by
  classical
  have h1 : ∑ z, dif A B z * conj (((ψ * η) z : ℂˣ) : ℂ) = ∑ z, dif A B z * conj ((ψ z : ℂˣ) : ℂ) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : z ∈ D
    · simp [hη z hz]
    · simp [hD z hz]
  rw [inner_dif, inner_dif] at h1
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 := mul_left_cancel₀ hc h1
  constructor
  · intro hψ
    have hB : ψ ∉ B := Finset.disjoint_left.mp hd hψ
    by_contra hn
    by_cases hb : ψ * η ∈ B <;> simp [hn, hψ, hB, hb] at h2
    norm_num at h2
  · intro hψ
    have hA : ψ ∉ A := Finset.disjoint_right.mp hd hψ
    by_contra hn
    by_cases ha : ψ * η ∈ A <;> simp [hn, hψ, hA, ha] at h2
    norm_num at h2

end UpperTheory.Zero.LLC.CharacterSumPairs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinNum
open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

def bd (g n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1)

private theorem geom (g : ℕ) (hg : 2 ≤ g) (M : ℕ) : ∑ d ∈ range (M + 1), g ^ d ≤ 2 * g ^ M := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [ih, Nat.mul_le_mul_left (g ^ k) hg]

theorem bd_le (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : bd g n ≤ 2 * g ^ (n / 2) := by
  unfold bd
  have hsub : ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1) ≤ ∑ p ∈ n.primeFactors, g ^ (n / p) :=
    Finset.sum_le_sum fun p _ => Nat.sub_le _ _
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Nat.dvd_of_mem_primeFactors hp
    have hq' := Nat.dvd_of_mem_primeFactors hq
    simp only at hpq
    rw [← Nat.div_div_self hp' hn.ne', hpq, Nat.div_div_self hq' hn.ne']
  have himg : ∑ p ∈ n.primeFactors, g ^ (n / p)
      = ∑ d ∈ n.primeFactors.image (fun p => n / p), g ^ d :=
    (Finset.sum_image hinj).symm
  have hsubset : n.primeFactors.image (fun p => n / p) ⊆ range (n / 2 + 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_left (Nat.prime_of_mem_primeFactors hp).two_le (by norm_num)
  calc _ ≤ _ := hsub
    _ = _ := himg
    _ ≤ ∑ d ∈ range (n / 2 + 1), g ^ d := Finset.sum_le_sum_of_subset hsubset
    _ ≤ 2 * g ^ (n / 2) := geom g hg (n / 2)

private theorem two_pow (m : ℕ) (hm : 6 ≤ m) : 8 * m + 1 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem big (g n : ℕ) (hg : 2 ≤ g) (hn : 12 ≤ n) : 2 * n * bd g n + 1 < g ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 6 ≤ m := by omega
    have hb := bd_le g (2 * m) hg (by omega)
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m) = g ^ m * g ^ m := by rw [two_mul, pow_add]
    rw [hp]
    generalize bd g (2 * m) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA]
  · have hm : 6 ≤ m := by omega
    have hb := bd_le g (2 * m + 1) hg (by omega)
    have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m + 1) = g ^ m * g ^ m * g := by rw [pow_succ, two_mul, pow_add]
    rw [hp]
    generalize bd g (2 * m + 1) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA, Nat.mul_le_mul_left (A * A) hg,
      Nat.mul_le_mul_right A hm]

private theorem pf2 : Nat.primeFactors 2 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf3 : Nat.primeFactors 3 = {3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf4 : Nat.primeFactors 4 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf5 : Nat.primeFactors 5 = {5} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf6 : Nat.primeFactors 6 = {2, 3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf7 : Nat.primeFactors 7 = {7} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf8 : Nat.primeFactors 8 = {2} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf9 : Nat.primeFactors 9 = {3} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf10 : Nat.primeFactors 10 = {2, 5} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]
private theorem pf11 : Nat.primeFactors 11 = {11} := by norm_num [Nat.primeFactors, Nat.primeFactorsList]

theorem bd_two (g : ℕ) : bd g 2 = g - 1 := by simp [bd, pf2]
theorem bd_three (g : ℕ) : bd g 3 = g - 1 := by simp [bd, pf3]
theorem bd_four (g : ℕ) : bd g 4 = g ^ 2 - 1 := by simp [bd, pf4]
theorem bd_five (g : ℕ) : bd g 5 = g - 1 := by simp [bd, pf5]
theorem bd_six (g : ℕ) : bd g 6 = (g ^ 3 - 1) + (g ^ 2 - 1) := by simp [bd, pf6]
theorem bd_seven (g : ℕ) : bd g 7 = g - 1 := by simp [bd, pf7]
theorem bd_eight (g : ℕ) : bd g 8 = g ^ 4 - 1 := by simp [bd, pf8]
theorem bd_nine (g : ℕ) : bd g 9 = g ^ 3 - 1 := by simp [bd, pf9]
theorem bd_ten (g : ℕ) : bd g 10 = (g ^ 5 - 1) + (g ^ 2 - 1) := by simp [bd, pf10]
theorem bd_eleven (g : ℕ) : bd g 11 = g - 1 := by simp [bd, pf11]

private theorem cast_pred (h c k : ℕ) (hc : 1 ≤ c) : (((h + c) ^ k - 1 : ℕ) : ℤ) = ((h : ℤ) + c) ^ k - 1 := by
  have h1 : 1 ≤ (h + c) ^ k := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

private theorem cast_pred1 (h c : ℕ) (hc : 1 ≤ c) : (((h + c) - 1 : ℕ) : ℤ) = ((h : ℤ) + c) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ h + c), Nat.cast_add, Nat.cast_one]

private theorem t2 (h : ℕ) : 2 * 2 * bd (h + 4) 2 + 1 < (h + 4) ^ 2 := by
  rw [bd_two]
  have e0 := cast_pred1 h 4 (by norm_num)
  have key : ((2 * 2 * ((h + 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 4) ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t3 (h : ℕ) : 2 * 3 * bd (h + 2) 3 + 1 < (h + 2) ^ 3 := by
  rw [bd_three]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 3 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 3 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t4 (h : ℕ) : 2 * 4 * bd (h + 3) 4 + 1 < (h + 3) ^ 4 := by
  rw [bd_four]
  have e0 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 4 * (((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 4 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t5 (h : ℕ) : 2 * 5 * bd (h + 2) 5 + 1 < (h + 2) ^ 5 := by
  rw [bd_five]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 5 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 5 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t6 (h : ℕ) : 2 * 6 * bd (h + 3) 6 + 1 < (h + 3) ^ 6 := by
  rw [bd_six]
  have e0 := cast_pred h 3 3 (by norm_num)
  have e1 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 6 * (((h + 3) ^ 3 - 1) + ((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 6 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t7 (h : ℕ) : 2 * 7 * bd (h + 2) 7 + 1 < (h + 2) ^ 7 := by
  rw [bd_seven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 7 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 7 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t8 (h : ℕ) : 2 * 8 * bd (h + 2) 8 + 1 < (h + 2) ^ 8 := by
  rw [bd_eight]
  have e0 := cast_pred h 2 4 (by norm_num)
  have key : ((2 * 8 * (((h + 2) ^ 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 8 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t9 (h : ℕ) : 2 * 9 * bd (h + 2) 9 + 1 < (h + 2) ^ 9 := by
  rw [bd_nine]
  have e0 := cast_pred h 2 3 (by norm_num)
  have key : ((2 * 9 * (((h + 2) ^ 3 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 9 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t10 (h : ℕ) : 2 * 10 * bd (h + 2) 10 + 1 < (h + 2) ^ 10 := by
  rw [bd_ten]
  have e0 := cast_pred h 2 5 (by norm_num)
  have e1 := cast_pred h 2 2 (by norm_num)
  have key : ((2 * 10 * (((h + 2) ^ 5 - 1) + ((h + 2) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 10 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t11 (h : ℕ) : 2 * 11 * bd (h + 2) 11 + 1 < (h + 2) ^ 11 := by
  rw [bd_eleven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 11 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 11 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

theorem two_bd (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n)
    (hex : ¬ ((g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6))) :
    2 * n * bd g n + 1 < g ^ n := by
  rcases le_or_gt 12 n with h12 | h12
  · exact big g n hg h12
  · interval_cases n
    · simp [bd]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 4 := ⟨g - 4, by omega⟩
      exact t2 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t3 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t4 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t5 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t6 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t7 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t8 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t9 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t10 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t11 k

theorem one_bd (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : n * bd g n + 1 < g ^ n := by
  by_cases hex : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)
  · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [bd_two]
      norm_num
    · rw [bd_two]
      norm_num
    · rw [bd_four]
      norm_num
    · rw [bd_six]
      norm_num
  · have h2 := two_bd g n hg hn hex
    linarith [Nat.mul_le_mul_right (bd g n) (show n ≤ 2 * n by omega)]

end UpperTheory.Zero.LLC.CharacterSumPairs
end

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

theorem exists_gen_char {G : Type} [CommGroup G] [Fintype G] [IsCyclic G] : ∃ η₀ : G →* ℂˣ,
    (∀ χ : G →* ℂˣ, ∃ t < Fintype.card G, χ = η₀ ^ t) ∧
    ∀ u v : ℕ, η₀ ^ u = η₀ ^ v ↔ u % Fintype.card G = v % Fintype.card G := by
  classical
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := G)
  have hN : 0 < Fintype.card G := Fintype.card_pos
  haveI : NeZero (Fintype.card G) := ⟨hN.ne'⟩
  have hox : orderOf x = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card]
  have hζ := Complex.isPrimitiveRoot_exp (Fintype.card G) hN.ne'
  let ζu : ℂˣ := (hζ.isUnit hN.ne').unit
  have hζu : IsPrimitiveRoot ζu (Fintype.card G) := hζ.isUnit_unit hN.ne'
  have hoζ : orderOf ζu = Fintype.card G := hζu.eq_orderOf.symm
  let η₀ : G →* ℂˣ := monoidHomOfForallMemZpowers hx (g' := ζu) (by rw [hoζ, hox])
  have hη : η₀ x = ζu := monoidHomOfForallMemZpowers_apply_gen hx _
  refine ⟨η₀, fun χ => ?_, fun u v => ?_⟩
  · have h1 : ((χ x : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hox, pow_orderOf_eq_one, map_one, Units.val_one]
    obtain ⟨t, ht, hteq⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨t, ht, ?_⟩
    rw [MonoidHom.eq_iff_eq_on_generator hx, MonoidHom.pow_apply, hη]
    ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hteq]
  · rw [MonoidHom.eq_iff_eq_on_generator hx, MonoidHom.pow_apply, MonoidHom.pow_apply, hη,
      pow_eq_pow_iff_modEq, hoζ]
    all_goals exact Iff.rfl

section Fld

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

theorem fin_of (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) : Finite K := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hr]; exact hn)
  exact Module.finite_of_finite (ZMod g)

theorem natCard_K (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) : Nat.card K = g ^ n := by
  haveI := fin_of hn hr
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hr]

theorem pow_iter {z : K} {d : ℕ} (h : z ^ g ^ d = z) (k : ℕ) : z ^ g ^ (d * k) = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem pow_of_deg (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : K)
    (hd : (minpoly (ZMod g) z).natDegree ≠ n) : ∃ p ∈ n.primeFactors, z ^ g ^ (n / p) = z := by
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hr]; exact hn)
  have hint : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  set d := (minpoly (ZMod g) z).natDegree with hd_def
  have hdpos : 0 < d := minpoly.natDegree_pos hint
  have hzd : z ^ g ^ d = z := by
    set F := IntermediateField.adjoin (ZMod g) {z}
    have hF : Module.finrank (ZMod g) F = d := IntermediateField.adjoin.finrank hint
    haveI := fin_of hdpos hF
    letI := Fintype.ofFinite F
    have hc : Fintype.card F = g ^ d := by
      rw [← Nat.card_eq_fintype_card]
      exact natCard_K hdpos hF
    have := FiniteField.pow_card (⟨z, IntermediateField.mem_adjoin_simple_self (ZMod g) z⟩ : F)
    rw [hc] at this
    simpa using congrArg Subtype.val this
  have hdvd : d ∣ n := hr ▸ minpoly.degree_dvd hint
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hd (by rw [hk, mul_one])
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, by rw [hk]; exact dvd_mul_of_dvd_right hpk d, hn.ne'⟩, ?_⟩
  rw [hk, Nat.mul_div_assoc d hpk]
  exact pow_iter hzd (k / p)

theorem unit_frob (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : Kˣ) : z ^ g ^ n = z := by
  haveI := fin_of hn hr
  letI := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_K hn hr
  ext
  push_cast
  rw [← hc, FiniteField.pow_card]

theorem char_frob (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) :
    θ ^ g ^ n = θ := by
  refine MonoidHom.ext (fun z => ?_)
  rw [MonoidHom.pow_apply, ← map_pow, unit_frob hn hr]

theorem exists_D [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    ∃ D : Finset Kˣ, (∀ z : Kˣ, z ∉ D → (minpoly (ZMod g) (z : K)).natDegree = n) ∧
      (∀ z ∈ D, ∃ p ∈ n.primeFactors, z ^ (g ^ (n / p) - 1) = 1) ∧ #D ≤ bd g n := by
  classical
  have key : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree ≠ n →
      ∃ p ∈ n.primeFactors, z ^ (g ^ (n / p) - 1) = 1 := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := pow_of_deg hn hr (z : K) hz
    refine ⟨p, hp, ?_⟩
    have hpos : 1 ≤ g ^ (n / p) := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
    have h2 : z ^ (g ^ (n / p) - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul]
      ext
      push_cast
      exact hpz
    exact mul_right_cancel h2
  refine ⟨Finset.univ.filter (fun z : Kˣ => (minpoly (ZMod g) (z : K)).natDegree ≠ n), ?_, ?_, ?_⟩
  · intro z hz
    by_contra h
    exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  · intro z hz
    exact key z (Finset.mem_filter.1 hz).2
  · calc #(Finset.univ.filter (fun z : Kˣ => (minpoly (ZMod g) (z : K)).natDegree ≠ n))
        ≤ #(n.primeFactors.biUnion
            (fun p => Finset.univ.filter (fun z : Kˣ => z ^ (g ^ (n / p) - 1) = 1))) := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨p, hp, hpz⟩ := key z (Finset.mem_filter.1 hz).2
          exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpz⟩⟩
      _ ≤ ∑ p ∈ n.primeFactors, #(Finset.univ.filter (fun z : Kˣ => z ^ (g ^ (n / p) - 1) = 1)) :=
          Finset.card_biUnion_le
      _ ≤ bd g n := by
          unfold bd
          refine Finset.sum_le_sum fun p hp => ?_
          have hpp := Nat.mem_primeFactors.1 hp
          have hle : p ≤ n := Nat.le_of_dvd hn hpp.2.1
          have hq : 0 < n / p := Nat.div_pos hle hpp.1.pos
          have hg2 : 1 < g ^ (n / p) := Nat.one_lt_pow hq.ne' (Fact.out : g.Prime).one_lt
          exact IsCyclic.card_pow_eq_one_le (by omega)

end Fld


open Classical in
noncomputable def cj {G : Type} [CommGroup G] (g n : ℕ) (θ : G →* ℂˣ) : Finset (G →* ℂˣ) := by
  classical
  exact (range n).image (fun j => θ ^ g ^ j)

theorem mem_cj {G : Type} [CommGroup G] {g n : ℕ} {θ χ : G →* ℂˣ} :
    χ ∈ cj g n θ ↔ ∃ j < n, θ ^ g ^ j = χ := by
  simp [cj]

theorem card_cj {G : Type} [CommGroup G] {g n : ℕ} {θ : G →* ℂˣ}
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) : #(cj g n θ) = n := by
  classical
  unfold cj
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

theorem sum_cj {G : Type} [CommGroup G] {g n : ℕ} {θ : G →* ℂˣ}
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) (z : G) :
    ∑ χ ∈ cj g n θ, ((χ z : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) := by
  classical
  unfold cj
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MonoidHom.pow_apply, map_pow]
  · intro i hi j hj hij
    exact hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

section Fld2

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem char_pow_pow_mul_eq_self_of_finrank (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n)
    (ψ : Kˣ →* ℂˣ) (m : ℕ) : ψ ^ g ^ (n * m) = ψ := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, char_frob hn hr]

theorem disj_cj (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ θ' : Kˣ →* ℂˣ)
    (hno : ¬ ∃ j < n, θ' = θ ^ g ^ j) : Disjoint (cj g n θ) (cj g n θ') := by
  rw [Finset.disjoint_left]
  intro χ h1 h2
  obtain ⟨i, hi, rfl⟩ := mem_cj.1 h1
  obtain ⟨j, hj, hj'⟩ := mem_cj.1 h2
  apply hno
  have e1 : θ' = θ ^ g ^ (i + (n - j)) := by
    calc θ' = θ' ^ g ^ n := (char_frob hn hr θ').symm
      _ = (θ' ^ g ^ j) ^ g ^ (n - j) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hj.le]
      _ = θ ^ g ^ (i + (n - j)) := by rw [hj', ← pow_mul, ← pow_add]
  refine ⟨(i + (n - j)) % n, Nat.mod_lt _ hn, ?_⟩
  rw [e1]
  conv_lhs => rw [← Nat.mod_add_div (i + (n - j)) n]
  rw [pow_add, pow_mul, char_pow_pow_mul_eq_self_of_finrank hn hr]

end Fld2

end UpperTheory.Zero.LLC.CharacterSumPairs
end

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

private def Reg (g n N t : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, (t * g ^ i) % N = (t * g ^ j) % N → i = j

private def Cl (g n N e t : ℕ) : Prop :=
  ∀ i < n, ∃ j < n, (t * g ^ i + e) % N = (t * g ^ j) % N

private instance (g n N t : ℕ) : Decidable (Reg g n N t) := by
  unfold Reg
  infer_instance

private instance (g n N e t : ℕ) : Decidable (Cl g n N e t) := by
  unfold Cl
  infer_instance

private def Pair (g n N e t t' : ℕ) : Prop :=
  (Reg g n N t ∧ Cl g n N e t) → (Reg g n N t' ∧ Cl g n N e t') → ∃ j < n, t' % N = (t * g ^ j) % N

private instance (g n N e t t' : ℕ) : Decidable (Pair g n N e t t') := by
  unfold Pair
  infer_instance

private theorem pairCheck_two_two : ∀ t < 2 ^ 2 - 1, ∀ t' < 2 ^ 2 - 1, Pair 2 2 (2 ^ 2 - 1) 1 t t' := by
  decide

private theorem pairCheck_three_two : ∀ t < 3 ^ 2 - 1, ∀ t' < 3 ^ 2 - 1, Pair 3 2 (3 ^ 2 - 1) 2 t t' := by
  decide

set_option maxHeartbeats 4000000 in
private theorem pairCheck_two_four : ∀ t < 2 ^ 4 - 1, ∀ t' < 2 ^ 4 - 1, Pair 2 4 (2 ^ 4 - 1) 3 t t' := by
  decide

set_option maxHeartbeats 40000000 in
private theorem pairCheck_two_six : ∀ t < 2 ^ 6 - 1, ∀ t' < 2 ^ 6 - 1, Pair 2 6 (2 ^ 6 - 1) 21 t t' := by
  decide

section

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem card_unitsK [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]

private theorem exc (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (e : ℕ)
    (he : ∀ p ∈ n.primeFactors, (g ^ (n / p) - 1) ∣ e)
    (hcheck : ∀ t < g ^ n - 1, ∀ t' < g ^ n - 1, Pair g n (g ^ n - 1) e t t')
    (θ θ' : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j)
    (hθ' : ∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j)
    (hs : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  by_contra hne
  have hdisj := disj_cj hn hr θ θ' hne
  obtain ⟨D, hD1, hD2, -⟩ := exists_D (K := K) (g := g) hn hr
  have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
    intro z hz
    unfold dif
    rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
  obtain ⟨η₀, hgen, hpow⟩ := exists_gen_char (G := Kˣ)
  have hcard := card_unitsK (K := K) (g := g) hn hr
  rw [hcard] at hgen hpow
  have key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) →
      (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) →
      Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s := by
    intro s hreg hcl
    unfold Reg Cl
    refine ⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩
    · rw [← pow_mul, ← pow_mul, hpow]
      exact hij
    · have hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s) := mem_cj.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := mem_cj.1 (hcl _ hm)
      refine ⟨j, hj, ?_⟩
      rw [← pow_mul, ← pow_mul, ← pow_add, hpow] at hjeq
      exact hjeq.symm
  have hηD : ∀ z ∈ D, (η₀ ^ e) z = 1 := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hD2 z hz
    obtain ⟨c, hc⟩ := he p hp
    rw [MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]
  have hmm := mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD
  obtain ⟨t, ht, rfl⟩ := hgen θ
  obtain ⟨t', ht', rfl⟩ := hgen θ'
  have hP := hcheck t ht t' ht'
  unfold Pair at hP
  obtain ⟨j, hj, hjt⟩ := hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ))
    (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))
  exact hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩

private theorem main (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) :
    (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
    ∀ θ' : Kˣ →* ℂˣ, (∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j) →
      (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
        ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
      ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hcard := card_unitsK (K := K) (g := g) hn hr
  obtain ⟨D, hD1, hD2, hDb⟩ := exists_D (K := K) (g := g) hn hr
  have hA := card_cj hθ
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    have hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0 := by
      intro z hz
      unfold dif
      rw [sum_cj hθ, hno z (hD1 z hz)]
      simp
    have hle := card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])
    rw [hA, hcard] at hle
    simp only [Finset.card_empty, add_zero] at hle
    have h1 := one_bd g n hg2 hn
    have h2 : D.card * n ≤ n * bd g n := by
      rw [mul_comm n]
      exact Nat.mul_le_mul_right n hDb
    omega
  · intro θ' hθ' hs
    by_cases hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
    · by_contra hne
      have hB := card_cj hθ'
      have hdisj := disj_cj hn hr θ θ' hne
      have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
        intro z hz
        unfold dif
        rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
      have hle := card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)
      rw [hA, hB, hcard] at hle
      have h1 := two_bd g n hg2 hn hex
      have h2 : D.card * (n + n) ≤ 2 * n * bd g n := by
        calc D.card * (n + n) ≤ bd g n * (n + n) := Nat.mul_le_mul_right _ hDb
          _ = 2 * n * bd g n := by ring
      omega

end

end UpperTheory.Zero.LLC.CharacterSumPairs

theorem UpperTheory.Zero.LLC.pin :
    UpperTheory.Zero.LLC.Pin := by
  unfold UpperTheory.Zero.LLC.Pin
  intro g _ n hn K _ _ hr θ hθ
  exact UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ
