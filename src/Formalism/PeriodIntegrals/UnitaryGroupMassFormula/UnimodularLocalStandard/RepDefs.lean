module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyDef

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def fvec {m : Type} [DecidableEq m] (a : ℕ) (b : ℤ) (d : ℕ) (lam : ℂ) (x y : ℤ) (i₀ : m) : m → ℂ :=
  Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))

def KeyHyps (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) : Prop :=
  CmOK a b c d ∧ IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ ∧ (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) ∧
  relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 ∧ relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
  l.Prime ∧ ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 ∧ i₀ ∉ T ∧
  (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))))

def ApproxAt (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (k : ℕ) (w : m → ℂ) : Prop :=
  SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧
    stdH (cmL a b d ha hd lam hlam) m w w =
      stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) * (1 + (l : ℂ) ^ k * p / q)

def KeyStart : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w

def KeyNewton : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∀ k, 1 ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w → ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 * k) w'

def KeyExact : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → ∃ K₀ : ℕ, ∀ k, K₀ ≤ k → ∀ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ k w →
    ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
      stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀)

theorem approx_pow_two (hN : KeyNewton) (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (w : m → ℂ) (hw : ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w) :
    ∀ n : ℕ, ∃ w', ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ (2 ^ n) w' := by
  intro n
  induction n with
  | zero => exact ⟨w, by simpa using hw⟩
  | succ n ih =>
    obtain ⟨w₁, hw₁⟩ := ih
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    obtain ⟨w₂, hw₂⟩ := hN a b c d ha hd lam hlam m Λ l x y T i₀ h (2 ^ n) (by omega) w₁ hw₁
    refine ⟨w₂, ?_⟩
    have he : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
    rw [he]
    exact hw₂

private theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ]
    omega

theorem keyRep_of (hS : KeyStart) (hN : KeyNewton) (hE : KeyExact) : KeyRep := by
  intro a b c d ha hd lam hlam hadm m _ _ Λ hsd hgen hi₁ hi₂ l hl x y hxy T i₀ hi₀ hT
  have h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ :=
    ⟨hadm, hsd, hgen, hi₁, hi₂, hl, hxy, hi₀, hT⟩
  obtain ⟨w, hw⟩ := hS a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨K₀, hK⟩ := hE a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨w', hw'⟩ := approx_pow_two hN a b c d ha hd lam hlam m Λ l x y T i₀ h w hw K₀
  exact hK (2 ^ K₀) (le_two_pow_self K₀) w' hw'

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.IsKTheta
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SelfDualStd
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma stdH_apply (L : PeriodPair) (m : Type*) [Fintype m] [DecidableEq m] (x y : m → ℂ) :
    stdH L m x y = (∑ i, x i * conj (y i)) * ((area L : ℝ) : ℂ)⁻¹ := by
  simp only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def detD (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

private theorem detD_eq_re_mul_im_sub (L : PeriodPair) :
    detD L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma detD_ne (L : PeriodPair) : detD L ≠ 0 := by
  intro h
  have h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0 := by rw [← detD_eq_re_mul_im_sub]; exact h
  have hi := LinearIndependent.pair_iff.mp L.indep
  have key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    apply hi
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      linarith
  obtain ⟨e1, e2⟩ := key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)
  obtain ⟨f1, f2⟩ := key L.ω₂.re (-L.ω₁.re) (by ring)
    (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)
  exact one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2)
    (by linear_combination (-1 : ℝ) * e2)).1

lemma area_eq (L : PeriodPair) : area L = |detD L| := rfl

lemma im_mul_conj (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by
  rw [detD_eq_re_mul_im_sub]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]
  ring

lemma coords (L : PeriodPair) (z : ℂ) : ∃ s t : ℝ, z = s • L.ω₁ + t • L.ω₂ := by
  refine ⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩
  have h := L.basis.sum_repr z
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
  exact h.symm

lemma int_of_div (L : PeriodPair) {t : ℝ} {k : ℤ} (h : t * detD L / area L = k) : ∃ j : ℤ, t = j := by
  have hD := detD_ne L
  rw [area_eq] at h
  rcases abs_choice (detD L) with hA | hA
  · rw [hA, mul_div_assoc, div_self hD, mul_one] at h
    exact ⟨k, h⟩
  · rw [hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one] at h
    exact ⟨-k, by push_cast; linarith⟩

lemma lattice_iff (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [← h]
    simp [zsmul_eq_mul, Complex.real_smul]
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [h]
    simp [zsmul_eq_mul, Complex.real_smul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section IsKsec
variable (b : ℤ) (d : ℕ)

def IsK (t : ℂ) : Prop := ∃ p q r : ℤ, r ≠ 0 ∧ (r : ℂ) * t = p + q * cmTheta b d

variable {b d}

lemma isK_int (n : ℤ) : IsK b d n := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨n, 0, 1, one_ne_zero, by simp⟩

lemma isK_theta : IsK b d (cmTheta b d) := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨0, 1, 1, one_ne_zero, by simp⟩

lemma isK_add {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨r' * p + r * p', r' * q + r * q', r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination (r' : ℂ) * h + (r : ℂ) * h'

lemma isK_neg {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨-p, -q, r, hr, ?_⟩
  push_cast
  linear_combination -h

lemma isK_sub {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by
  rw [sub_eq_add_neg]
  exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add h (PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg h')

private lemma conj_cmTheta : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
  unfold cmTheta
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

lemma isK_conj {t : ℂ} (h : IsK b d t) : IsK b d (conj t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  have h2 : (r : ℂ) * conj t = p + q * conj (cmTheta b d) := by
    have h3 := congrArg conj h
    simpa using h3
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p + q * b, -q, r, hr, ?_⟩
  rw [h2, PI.UnitaryGroupMassFormula.UnimodLocStd.conj_cmTheta]
  push_cast
  ring

variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn

lemma isK_mul {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t * t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p * p' - q * q' * e, p * q' + q * p' + q * q' * b, r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination ((r' : ℂ) * t') * h + ((p : ℂ) + q * cmTheta b d) * h' - ((q : ℂ) * q') * hn

lemma isK_inv {t : ℂ} (h : IsK b d t) : IsK b d t⁻¹ := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
    simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  obtain ⟨p, q, r, hr, h⟩ := h
  have hrt : (r : ℂ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) ht

  have hz : ((p ^ 2 + p * q * b + q ^ 2 * e : ℤ) : ℂ) =
      (r : ℂ) * t * (p + q * b - q * cmTheta b d) := by
    rw [h]
    push_cast
    linear_combination (-(q : ℂ) ^ 2) * hn
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  by_cases hN : p ^ 2 + p * q * b + q ^ 2 * e = 0
  ·
    have hw : (p : ℂ) + q * b - q * cmTheta b d = 0 := by
      have h0 : (r : ℂ) * t * (p + q * b - q * cmTheta b d) = 0 := by
        rw [← hz, hN, Int.cast_zero]
      exact (mul_eq_zero.mp h0).resolve_left hrt
    have hk : (r : ℂ) * t = ((2 * p + q * b : ℤ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination -hw
    have hk0 : (2 * p + q * b : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hk
      exact hrt hk
    refine ⟨r, 0, 2 * p + q * b, hk0, ?_⟩
    rw [← hk, mul_inv_cancel_right₀ ht]
    simp
  · refine ⟨r * (p + q * b), -(r * q), p ^ 2 + p * q * b + q ^ 2 * e, hN, ?_⟩
    rw [hz]
    field_simp
    push_cast
    ring

lemma isK_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end IsKsec

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
