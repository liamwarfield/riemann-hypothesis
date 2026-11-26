module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLprim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.FeLFunctionConstMul
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.GaussMulGaussInv
open Finset UpperTheory.V.Bern

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar :=
    funext fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h1 := congr_fun (ZMod.dft_dft (⇑χ)) 1
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h1
  simp only at h1
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one,
    smul_eq_mul] at h1
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]

private theorem conj_gauss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)
  rw [inv_inv, Units.val_neg, Units.val_one] at h
  rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]

theorem UpperTheory.V.Bern.b_gauss :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N ∧ ‖χ.rootNumber‖ = 1 := by
  intro N _ χ hχ
  have hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N := by
    rw [← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]
  have hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by exact_mod_cast hns
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    rw [Complex.norm_def, hns']
  refine ⟨hg, ?_⟩
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one,
    hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_ne_zero'.mpr hpos)
end

open Finset UpperTheory.V.Bern

private lemma fe_LFunction_const_mul {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem UpperTheory.V.Bern.b_fe :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), χ.IsPrimitive → 1 ≤ k → χ (-1) = (-1) ^ k → ‖χ.LFunction (1 - k)‖ = 2 * ((k - 1).factorial : ℝ) * (N : ℝ) ^ ((k : ℝ) - 1 / 2) / (2 * Real.pi) ^ k * ‖χ⁻¹.LFunction k‖ := by
  intro N _ χ k hχ hk hpar
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set g := gaussSum χ ZMod.stdAddChar with hg
  have hinv1 : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg_one]
  have hF : ZMod.dft (χ : ZMod N → ℂ) = fun j => (χ (-1) * g) * χ⁻¹ j := by
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, show -j = -1 * j by ring, map_mul, hinv1]
    ring
  have hF' : ZMod.dft (fun x => χ (-x)) = fun j => g * χ⁻¹ j := by
    rw [ZMod.dft_comp_neg]
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    ring
  have hs : ∀ n : ℕ, ((m + 1 : ℕ) : ℂ) ≠ -n := by
    intro n h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hs' : χ 0 = 0 ∨ ((m + 1 : ℕ) : ℂ) ≠ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      apply χ.map_zero'
      rintro rfl
      have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [h1, map_one] at hpar
      norm_num at hpar
    · right
      exact_mod_cast (by omega : m + 1 ≠ 1)
  have hfe := ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'
  rw [hF, hF', fe_LFunction_const_mul, fe_LFunction_const_mul] at hfe
  have he1 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = Complex.I ^ (m + 1) := by
    rw [show (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  have he2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = (-Complex.I) ^ (m + 1) := by
    rw [show -(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  have hGam : Complex.Gamma ((m + 1 : ℕ) : ℂ) = (m.factorial : ℂ) := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have key : ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ)) =
      (N : ℂ) ^ (((m + 1 : ℕ) : ℂ) - 1) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ)) *
        (m.factorial : ℂ) * g * ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) *
        (2 * (-Complex.I) ^ (m + 1)) := by
    rw [hfe, he1, he2, hGam, hpar, ← h2pi, neg_pow Complex.I]
    ring
  show ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ))‖ = _
  rw [key]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), (b_gauss χ hχ).1]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_natCast]
  have hre1 : (((m + 1 : ℕ) : ℂ) - 1).re = ((m : ℕ) : ℝ) := by simp
  have hre2 : (-((m + 1 : ℕ) : ℂ)).re = -((m + 1 : ℕ) : ℝ) := by simp
  have hL : DirichletCharacter.LFunction χ⁻¹ ((m + 1 : ℕ) : ℂ) = ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) := rfl
  have hNr : (N : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) ^ m * √(N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  rw [hre1, hre2, Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast, hL, hNr,
    Nat.add_sub_cancel, Complex.norm_two]
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (m + 1) := by positivity
  field_simp
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_nzC :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro N _ χ k hk hpar
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hpar' : χ.primitiveCharacter (-1) = (-1) ^ k := by rw [(b_parity k χ).2, hpar]
  have hne1 : χ.primitiveCharacter⁻¹ ≠ 1 ∨ (k : ℂ) ≠ 1 := by
    rcases Nat.lt_or_ge 1 k with h | h
    · right
      exact_mod_cast (ne_of_gt h)
    · left
      have hk1 : k = 1 := le_antisymm h hk
      intro h1
      have h1' : χ.primitiveCharacter = 1 := inv_eq_one.mp h1
      rw [h1', MulChar.one_apply isUnit_one.neg, hk1, pow_one] at hpar'
      norm_num at hpar'
  have hL := b_fe χ.primitiveCharacter k hprim hk hpar'
  have hLne : DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hne1 (by simp; exact_mod_cast hk)
  have hB : Bprim k χ ≠ 0 := by
    intro h0
    have hl := (b_lprim χ.primitiveCharacter k hk).1
    have hg : genB k ⇑χ.primitiveCharacter = 0 := h0
    rw [hg, neg_zero, zero_div] at hl
    rw [hl, norm_zero] at hL
    have hc : (0 : ℝ) < (χ.conductor : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hpos : (0 : ℝ) < 2 * ((k - 1).factorial : ℝ) * (χ.conductor : ℝ) ^ ((k : ℝ) - 1 / 2)
        / (2 * Real.pi) ^ k * ‖DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ)‖ := by
      apply mul_pos
      · apply div_pos
        · apply mul_pos
          · positivity
          · exact Real.rpow_pos_of_pos hc _
        · positivity
      · exact norm_pos_iff.mpr hLne
    linarith
  refine ⟨hB, fun hk2 => ?_⟩
  rw [b_primlevel k χ (Nat.pos_of_ne_zero (NeZero.ne N)) hk]
  refine mul_ne_zero hB ?_
  rw [Finset.prod_ne_zero_iff]
  intro p hp h0
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have heq : primVal χ p * (p : ℂ) ^ (k - 1) = 1 := by linear_combination -h0
  have hv : ‖primVal χ p‖ = 0 ∨ ‖primVal χ p‖ = 1 := by
    by_cases hu : IsUnit (p : ZMod χ.conductor)
    · right
      have := χ.primitiveCharacter.unit_norm_eq_one hu.unit
      rwa [IsUnit.unit_spec] at this
    · left
      simp [primVal, MulChar.map_nonunit _ hu]
  have hn := congrArg norm heq
  rw [norm_mul, norm_pow, Complex.norm_natCast, norm_one] at hn
  rcases hv with h | h
  · rw [h, zero_mul] at hn
    exact zero_ne_one hn
  · rw [h, one_mul] at hn
    have hn' : p ^ (k - 1) = 1 := by exact_mod_cast hn
    rcases Nat.pow_eq_one.mp hn' with h1 | h1
    · exact hpp.one_lt.ne' h1
    · omega
