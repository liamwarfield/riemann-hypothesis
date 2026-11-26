module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.HNsmulNsmul
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.DescentStep
noncomputable section
open scoped ComplexConjugate
open Polynomial

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma pigeon {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (A B E : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hB : ¬ (p : ℤ) ∣ B) : ∃ s t : ℤ, (p : ℤ) ∣ s ^ 2 * A + t ^ 2 * B - E := by
  have := Fact.mk hp
  have hA' : (A : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB' : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']
    rfl
  have hg : (C (B : ZMod p) * X ^ 2).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB']
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  linear_combination hxy

variable {a : ℕ} {b c : ℤ} {d : ℕ}

lemma descent_step (hok : CmOK a b c d) {P Q r p q : ℤ} (hr : (d : ℤ) ∣ r) (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hM : r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q) :
    (d : ℤ) ∣ P ∧ (d : ℤ) ∣ Q := by
  obtain ⟨h4, -, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef
  have hcop : IsCoprime ((d : ℤ) ^ 2) q :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)
  have hdN : (d : ℤ) ^ 2 ∣ N := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hM]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _
  have hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2 := by
    rw [hNdef]
    linear_combination Q ^ 2 * h4
  have hX : (d : ℤ) ∣ 2 * P + b * Q := by
    apply hD.dvd_of_dvd_pow (n := 2)
    have : (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2 := by rw [hid]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)
  have hQ2 : (d : ℤ) ∣ Q ^ 2 := by
    have h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2 := by
      have : (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2 := by rw [hid]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_left hD0).mp h1
  have hQ : (d : ℤ) ∣ Q := hD.dvd_of_dvd_pow hQ2
  have h2P : (d : ℤ) ∣ 2 * P := by
    have : 2 * P = (2 * P + b * Q) - b * Q := by ring
    rw [this]
    exact dvd_sub hX (Dvd.dvd.mul_left hQ _)
  refine ⟨?_, hQ⟩
  rcases hD.dvd_or_dvd h2P with h | h
  · exact absurd h hD2
  · exact h

lemma norm_square (hok : CmOK a b c d) {γ : ℂ} (hγ : IsK b d γ) {p q : ℤ} (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hN : γ * conj γ = (p : ℂ) / q) : ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
  obtain ⟨h4, ha, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero _)
  have hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
    have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    have h4' : (4 * a * c : ℂ) = b ^ 2 + d := by exact_mod_cast h4
    unfold cmTheta
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs +
      (-1 / 4 : ℂ) * h4'

  have rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
    intro P Q r hr
    have h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q) := by
      rw [map_mul, map_intCast, ← hN]
      ring
    have h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c) := by
      rw [hr, map_add (f := _), map_mul, map_intCast, map_intCast, theta_conj]
      linear_combination (Q : ℂ) ^ 2 * hθ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
      rw [← h2, h1]
      field_simp
    exact_mod_cast hC

  have main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q r hn hr0 hM
      by_cases hdr : (d : ℤ) ∣ r
      · obtain ⟨hP, hQ⟩ := descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM
        obtain ⟨P', rfl⟩ := hP
        obtain ⟨Q', rfl⟩ := hQ
        obtain ⟨r', rfl⟩ := hdr
        have hr' : r' ≠ 0 := by
          rintro rfl
          simp at hr0
        have hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q := by
          have hd2 : ((d : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hD0
          apply mul_left_cancel₀ hd2
          linear_combination hM
        refine ih r'.natAbs ?_ P' Q' r' rfl hr' hM'
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (d : ℤ).natAbs := by
          have := hdp.two_le
          simp only [Int.natAbs_natCast]
          omega
        have h2 : 0 < r'.natAbs := Int.natAbs_pos.mpr hr'
        nlinarith
      · have := Fact.mk hdp
        have hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q) := by
          linear_combination 4 * hM + q * Q ^ 2 * h4
        have h2r : ((2 * r : ℤ) : ZMod d) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro h
          rcases hD.dvd_or_dvd h with h | h
          · exact hD2 h
          · exact hdr h
        refine ⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hk := congrArg (Int.cast : ℤ → ZMod d) hkey
        push_cast at hk h2r ⊢
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at *
        have hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h2r, one_pow]
        linear_combination (-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv
  obtain ⟨P, Q, r, hr0, hr⟩ := hγ
  exact main r.natAbs P Q r rfl hr0 (rel P Q r hr)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

lemma kappa_real : conj (repKappa a b d ha hd lam hlam) = repKappa a b d ha hd lam hlam := by
  unfold repKappa
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_natCast]

lemma not_dvd_mul' {l : ℕ} (hl : l.Prime) {u v : ℤ} (hu : ¬ (l : ℤ) ∣ u) (hv : ¬ (l : ℤ) ∣ v) :
    ¬ (l : ℤ) ∣ u * v := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h1 | h1
  · exact hu h1
  · exact hv h1

lemma H_nsmul_nsmul (L : PeriodPair) (s t : ℕ) (v w : m → ℂ) :
    stdH L m (s • v) (t • w) = (s : ℂ) * t * stdH L m v w := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Pi.mul_apply, Pi.natCast_apply, map_mul, map_natCast]
    ring

lemma H_self_ne (L : PeriodPair) {v : m → ℂ} (hv : v ≠ 0) : stdH L m v v ≠ 0 := by
  rw [stdH_apply]
  have hA : area L ≠ 0 := by rw [area_eq]; exact abs_ne_zero.mpr (detD_ne L)
  refine mul_ne_zero ?_ (inv_ne_zero (by exact_mod_cast hA))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push_neg at h; exact hv (funext h)
  have hsum : (∑ j, v j * conj (v j)) = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun j _ => Complex.mul_conj (v j)
  rw [hsum]
  have : 0 < ∑ j, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  exact_mod_cast this.ne'

variable {a b c d ha hd lam hlam m}

lemma sat_norm (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) :
    ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧ stdH (cmL a b d ha hd lam hlam) m v v = repKappa a b d ha hd lam hlam * p / q := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨n, hn⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  refine ⟨n, (s : ℤ) * s, not_dvd_mul' hl hs' hs', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma sat_pair (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) :
    ∃ n c₂ s : ℤ, ¬ (l : ℤ) ∣ s ∧ stdH (cmL a b d ha hd lam hlam) m v w =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨t, ht, htw⟩ := hw
  obtain ⟨n, c₂, hn, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv htw
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  have ht' : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => ht (by exact_mod_cast h)
  refine ⟨n, c₂, (s : ℤ) * t, not_dvd_mul' hl hs' ht', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h; apply ht; rw [show t = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma im_pi_inv (n c₂ : ℤ) :
    ((2 * cmTheta b d - b)⁻¹ * (repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)))).im =
      -((2 * n - c₂ * b : ℤ) : ℝ) / d := by
  rw [rep_kappa_eq]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hd').ne'
  have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd'.le
  have hpi : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    unfold cmTheta
    ring
  have hconj : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
    unfold cmTheta
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hpi, hconj]
  simp [Complex.mul_im, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq, Complex.div_re,
    Complex.div_im]
  field_simp
  rw [show (Real.sqrt d) ^ 2 = d by rw [sq]; exact hsq] at *
  ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def UnitVecRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m]
    [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (x0 y0 : ℤ) (T : Finset m) (i₀ : m),
    KeyHyps a b c d ha hd lam hlam m Λ d x0 y0 T i₀ →
    ∀ x : m → ℂ, SatMem d Λ x → (∀ j ∈ T, x j = 0) →
      (x = 0 ∨ ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * p / q) →
    ∀ z₀ : m → ℂ, SatMem d Λ z₀ → (∀ j ∈ T, z₀ j = 0) → stdH (cmL a b d ha hd lam hlam) m z₀ x = 0 → z₀ ≠ 0 →
    ∃ y : m → ℂ, SatMem d Λ y ∧ (∀ j ∈ T, y j = 0) ∧ stdH (cmL a b d ha hd lam hlam) m y x = 0 ∧
      ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m y y = repKappa a b d ha hd lam hlam * p / q

end PI.UnitaryGroupMassFormula.UnimodLocStd
