module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepBasic
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Form

variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]

theorem rep_H_apply (z w : m → ℂ) :
    stdH L m z w = ((area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem rep_H_conj (z w : m → ℂ) : conj (stdH L m z w) = stdH L m w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rep_H_apply, rep_H_apply, map_mul, map_sum]
  congr 1
  · simp [Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]

theorem rep_H_re (z : m → ℂ) : ((stdH L m z z).re : ℂ) = stdH L m z z :=
  Complex.conj_eq_iff_re.mp (rep_H_conj L m z z)

end Form

section Sat

variable {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ))

theorem rep_sat_of_mem {v : m → ℂ} (hv : v ∈ Λ) (hl : l.Prime) : SatMem l Λ v :=
  ⟨1, by simpa using hl.one_lt.ne' ∘ Nat.dvd_one.mp, by simpa using hv⟩

theorem rep_sat_add (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v + w) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨k, hk, hkw⟩ := hw
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (v + w) = k • (n • v) + n • (k • w) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply]; ring
  rw [e]
  exact Λ.add_mem (Λ.nsmul_mem hnv k) (Λ.nsmul_mem hkw n)

theorem rep_sat_neg {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (-v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  exact ⟨n, hn, by rw [smul_neg]; exact Λ.neg_mem hnv⟩

theorem rep_sat_sub (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v - w) := by
  rw [sub_eq_add_neg]; exact rep_sat_add l Λ hl hv (rep_sat_neg l Λ hw)

theorem rep_sat_ratN (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) (k : ℕ) (hk : ¬ l ∣ k) :
    SatMem l Λ (((r : ℂ) / k) • v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h; exact hk (by rw [Nat.cast_eq_zero.mp h]; exact dvd_zero _)
  refine ⟨n * k, fun h => (hl.dvd_mul.mp h).elim hn hk, ?_⟩
  have e : (n * k) • (((r : ℂ) / k) • v) = r • (n • v) := by
    funext i; simp only [Pi.smul_apply, nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply, Pi.intCast_apply]; field_simp
  rw [e]
  exact Λ.zsmul_mem hnv _

theorem rep_sat_rat (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) (r s : ℤ) (hs : ¬ (l : ℤ) ∣ s) :
    SatMem l Λ (((r : ℂ) / s) • v) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · simpa using rep_sat_ratN l Λ hl hv r k (fun h => hs (Int.natCast_dvd_natCast.mpr h))
  · have := rep_sat_ratN l Λ hl hv (-r) k (fun h => hs (by simpa using Int.natCast_dvd_natCast.mpr h))
    convert this using 2
    push_cast; rw [div_neg, neg_div]

end Sat

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Arith

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem rep_sqrt_sq : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_natCast]

theorem rep_conj_theta : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [cmTheta, map_div₀, map_add (f := _), map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat]
  ring

theorem rep_theta_add_conj : cmTheta b d + conj (cmTheta b d) = b := by
  rw [rep_conj_theta b d, cmTheta]
  ring

theorem rep_theta_mul_conj (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * conj (cmTheta b d) = (a : ℂ) * c := by
  have h4 : ((4 * (a : ℤ) * c : ℤ) : ℂ) = ((b ^ 2 + d : ℤ) : ℂ) := by rw [hOK]
  push_cast at h4
  have hs := rep_sqrt_sq d
  rw [rep_conj_theta b d, cmTheta]
  linear_combination (-1 / 4 : ℂ) * h4 - (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq +
    (1 / 4 : ℂ) * hs

theorem rep_elt_norm (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (p q : ℤ) :
    (lam * ((p : ℂ) * a + q * cmTheta b d)) * conj (lam * ((p : ℂ) * a + q * cmTheta b d)) =
      (Complex.normSq lam : ℂ) * a * ((a * p ^ 2 + b * p * q + c * q ^ 2 : ℤ) : ℂ) := by
  have h1 := rep_theta_add_conj b d
  have h2 := rep_theta_mul_conj a b c d hOK
  have hN := Complex.mul_conj lam
  simp only [map_mul, map_add (f := _), map_intCast, map_natCast]
  push_cast
  linear_combination ((p : ℂ) * a + q * cmTheta b d) * ((p : ℂ) * a + q * conj (cmTheta b d)) * hN +
    (Complex.normSq lam : ℂ) * p * q * a * h1 + (Complex.normSq lam : ℂ) * q ^ 2 * h2

theorem rep_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
theorem rep_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

theorem rep_area_ne : area (cmL a b d ha hd lam hlam) ≠ 0 := by
  rw [area, rep_omega1, rep_omega2, abs_ne_zero]
  have him : (conj (lam * a) * (lam * cmTheta b d)).im =
      Complex.normSq lam * a * (Real.sqrt d / 2) := by
    rw [show conj (lam * a) * (lam * cmTheta b d) = (lam * conj lam) * a * cmTheta b d by
      simp only [map_mul, map_natCast]; ring, Complex.mul_conj,
      show ((Complex.normSq lam : ℝ) : ℂ) * a * cmTheta b d =
        ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d by push_cast; ring, Complex.im_ofReal_mul]
    simp [cmTheta]
  rw [him]
  exact ne_of_gt (mul_pos (mul_pos (Complex.normSq_pos.2 hlam) (Nat.cast_pos.2 ha))
    (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)) two_pos))

def repKappa : ℂ := ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * (Complex.normSq lam : ℂ) * a

theorem rep_kappa_ne : repKappa a b d ha hd lam hlam ≠ 0 := by
  unfold repKappa
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.2 (rep_area_ne a b d ha hd lam hlam)))
    (Complex.ofReal_ne_zero.2 (Complex.normSq_pos.2 hlam).ne')) (Nat.cast_ne_zero.2 ha.ne')

variable (m : Type) [Fintype m] [DecidableEq m]

theorem rep_norm_f (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (x y : ℤ) (i₀ : m) :
    stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
      repKappa a b d ha hd lam hlam * ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) := by
  rw [rep_H_apply, Fintype.sum_eq_single i₀ (fun i hi => by simp [fvec, hi])]
  simp only [fvec, Pi.single_eq_same]
  rw [rep_elt_norm a b c d lam hOK x y]
  unfold repKappa
  ring

theorem rep_fvec_mem (x y : ℤ) (i₀ : m) : fvec a b d lam x y i₀ ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup]
  intro i
  by_cases h : i = i₀
  · subst h
    simp only [fvec, Pi.single_eq_same]
    exact PeriodPair.mem_lattice.2 ⟨x, y, by rw [rep_omega1, rep_omega2]; ring⟩
  · simp only [fvec, Pi.single_eq_of_ne h]
    exact zero_mem _

end Arith

end PI.UnitaryGroupMassFormula.UnimodLocStd
