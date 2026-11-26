module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepPrimPair
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_coord (a : ℕ) (ha : 0 < a) (b : ℤ) (d : ℕ) (hd : 0 < d) (p q r s : ℝ)
    (h : (p : ℂ) * a + q * cmTheta b d = r * a + s * cmTheta b d) : p = r ∧ q = s := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [cmTheta] at him hre
  have hqs : q = s := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by omega)
  subst hqs
  refine ⟨?_, rfl⟩
  have h3 : p * a = r * a := by linarith
  exact mul_right_cancel₀ ha'.ne' h3

theorem rep_prim_pair (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) :
    ∃ xt : m → ℂ, xt ∈ Λ ∧ (∀ j ∈ T, xt j = 0) ∧ ∃ yv : m → ℂ, yv ∈ Λ ∧ ∃ c₂ : ℤ,
      (stdH (cmL a b d ha hd lam hlam) m xt yv).im = c₂ ∧ ¬ (l : ℤ) ∣ c₂ := by
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set f := fvec a b d lam x y i₀ with hfdef
  have hfstd : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  unfold relIdx at h1 h2
  set Df := (Λ.relIndex (stdLat L m)).factorial with hDf
  set Nf := ((stdLat L m).relIndex Λ).factorial with hNf
  have hDfΛ : Df • f ∈ Λ :=
    (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h2 hfstd
      (fun j hj hle => Nat.dvd_factorial hj hle)).1
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlam0 := hlam

  set P : ℕ → Prop := fun j => ((l : ℂ) ^ j)⁻¹ • (Df • f) ∈ Λ with hPdef
  have hex : ∃ j, ¬ P j := by
    by_contra hall
    push_neg at hall
    set K : ℕ := Nf * Df with hK
    have hK0 : K ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    have hdvd : ∀ j : ℕ, (l : ℤ) ^ j ∣ K * x ∧ (l : ℤ) ^ j ∣ K * y := by
      intro j
      have hmem : Nf • (((l : ℂ) ^ j)⁻¹ • (Df • f)) ∈ stdLat L m :=
        (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h1 (hall j)
          (fun j hj hle => Nat.dvd_factorial hj hle)).1
      obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hmem i₀ (Set.mem_univ i₀))
      rw [rep_omega1, rep_omega2] at hpq
      simp only [hfdef, fvec, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, smul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hpq
      have hlj : ((l : ℂ) ^ j) ≠ 0 := pow_ne_zero _ hl0
      have e : ((p : ℝ) : ℂ) * a + ((q : ℝ) : ℂ) * cmTheta b d =
          (((K * x : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * a + (((K * y : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * cmTheta b d := by
        apply mul_left_cancel₀ hlam
        push_cast
        rw [hK]; push_cast
        linear_combination hpq
      obtain ⟨ep, eq'⟩ := rep_coord a ha b d hd _ _ _ _ e
      have hlj' : ((l : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
      refine ⟨⟨p, ?_⟩, ⟨q, ?_⟩⟩
      · rw [eq_div_iff hlj'] at ep
        have : ((K * x : ℤ) : ℝ) = ((l ^ j * p : ℤ) : ℝ) := by push_cast at ep ⊢; linear_combination -ep
        exact_mod_cast this
      · rw [eq_div_iff hlj'] at eq'
        have : ((K * y : ℤ) : ℝ) = ((l ^ j * q : ℤ) : ℝ) := by push_cast at eq' ⊢; linear_combination -eq'
        exact_mod_cast this
    set J := K * (x.natAbs + y.natAbs) + 1
    have hJ : K * (x.natAbs + y.natAbs) < l ^ J :=
      lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.lt_pow_self hl.one_lt).le)
    have hx0 : K * x = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).1
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * x.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ < l ^ J := hJ
    have hy0 : K * y = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).2
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * y.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ < l ^ J := hJ
    have hK0' : (K : ℤ) ≠ 0 := by exact_mod_cast hK0
    have hx : x = 0 := (mul_eq_zero.mp hx0).resolve_left hK0'
    have hy : y = 0 := (mul_eq_zero.mp hy0).resolve_left hK0'
    apply hQ; rw [hx, hy]; simp
  classical
  set j₁ := Nat.find hex with hj₁
  have hP0 : P 0 := by simp only [hPdef, pow_zero, inv_one, one_smul]; exact hDfΛ
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj₁, h0] at this
    exact this hP0
  have hPprev : P (j₁ - 1) := by
    have := Nat.find_min hex (show j₁ - 1 < Nat.find hex by omega)
    simpa using this
  have hPj : ¬ P j₁ := Nat.find_spec hex
  set xt := ((l : ℂ) ^ (j₁ - 1))⁻¹ • (Df • f) with hxt
  have hxtΛ : xt ∈ Λ := hPprev
  have hxtT : ∀ j ∈ T, xt j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := by rintro rfl; exact hi₀ hj
    simp [hxt, hfdef, fvec, Pi.single_apply, hne]
  have hdiv : ((l : ℂ)⁻¹) • xt ∉ Λ := by
    rw [hxt, smul_smul, ← mul_inv, ← pow_succ', show j₁ - 1 + 1 = j₁ by omega]
    exact hPj
  refine ⟨xt, hxtΛ, hxtT, ?_⟩
  have hnd : ¬ ∀ yv ∈ Λ, ∃ k : ℤ, altE (stdH L m) ((l : ℂ)⁻¹ • xt) yv = k := by
    intro hall
    apply hdiv
    have : ((l : ℂ)⁻¹ • xt) ∈ dualLat (stdH L m) Λ := hall
    rw [hΛ] at this
    exact this
  push_neg at hnd
  obtain ⟨yv, hyv, hyk⟩ := hnd
  have hxtd : xt ∈ dualLat (stdH L m) Λ := by rw [hΛ]; exact hxtΛ
  obtain ⟨c₂, hc₂⟩ := hxtd yv hyv
  refine ⟨yv, hyv, c₂, hc₂, ?_⟩
  rintro ⟨t, rfl⟩
  apply hyk t
  simp only [altE] at hc₂ ⊢
  have e : (stdH L m ((l : ℂ)⁻¹ • xt) yv) = (((l : ℝ)⁻¹ : ℝ) : ℂ) * stdH L m xt yv := by
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, Complex.im_ofReal_mul, hc₂]
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  push_cast
  field_simp

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamDef
namespace PI.UnitaryGroupMassFormula.UnimodLocStd

def KeyStartRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → l = d → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRepModl
namespace PI.UnitaryGroupMassFormula.UnimodLocStd

open Polynomial in
theorem rep_rep_modl {l : ℕ} (hl : l.Prime) (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hld : ¬ (l : ℤ) ∣ d) (N S Q0 : ℤ) (hN : ¬ (l : ℤ) ∣ N) (hS : ¬ (l : ℤ) ∣ S) (hQ : ¬ (l : ℤ) ∣ Q0) :
    ∃ s t : ℤ, (l : ℤ) ∣ (s ^ 2 + b * s * t + a * c * t ^ 2) * N - Q0 * S := by
  have normForm_surj_zmod_lemma {l : ℕ} [Fact l.Prime] (A B : ZMod l) (D : ZMod l)
      (hOK : 4 * A = B ^ 2 + D) (hD : D ≠ 0) (v : ZMod l) (hv : v ≠ 0) :
      ∃ s t : ZMod l, s ^ 2 + B * s * t + A * t ^ 2 = v := by
    have hl : l.Prime := Fact.out
    rcases hl.eq_two_or_odd with rfl | hodd
    · refine ⟨1, 0, ?_⟩
      have h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
        intro x hx; fin_cases x
        · exact absurd rfl hx
        · rfl
      rw [h1 v hv]; ring
    · have hl2 : l ≠ 2 := by omega
      have h2 : (2 : ZMod l) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hl2)
      have hcard : Fintype.card (ZMod l) % 2 = 1 := by rw [ZMod.card]; exact hodd
      open Polynomial in
      have hf : ((X : (ZMod l)[X]) ^ 2).degree = 2 := by
        rw [degree_X_pow]; rfl
      open Polynomial in
      have hdeg : (C D * X ^ 2 : (ZMod l)[X]).degree = 2 := by
        rw [degree_C_mul_X_pow 2 hD]; rfl
      open Polynomial in
      have hg : (C D * X ^ 2 - C (4 * v) : (ZMod l)[X]).degree = 2 := by
        rw [degree_sub_C (by rw [hdeg]; decide), hdeg]
      obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
      simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C] at hxy
      set i : ZMod l := (2 : ZMod l)⁻¹ with hi_def
      have hi : 2 * i = 1 := mul_inv_cancel₀ h2
      refine ⟨(x - B * y) * i, y, ?_⟩
      have h4 : (4 : ZMod l) ≠ 0 := by
        have : (4 : ZMod l) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      apply mul_left_cancel₀ h4
      linear_combination hxy + y ^ 2 * hOK + ((2 * i + 1) * (x - B * y) ^ 2 + 2 * B * y * (x - B * y)) * hi
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have nz : ∀ z : ℤ, ¬ (l : ℤ) ∣ z → (z : ZMod l) ≠ 0 := fun z hz h =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z l).mp h)
  have hOK' : 4 * (((a : ℤ) : ZMod l) * (c : ZMod l)) = (b : ZMod l) ^ 2 + ((d : ℤ) : ZMod l) := by
    have := congrArg (Int.cast : ℤ → ZMod l) hOK
    push_cast at this ⊢
    linear_combination this
  have hN' := nz N hN
  obtain ⟨s, t, hst⟩ := normForm_surj_zmod_lemma (((a : ℤ) : ZMod l) * (c : ZMod l)) (b : ZMod l)
    ((d : ℤ) : ZMod l) hOK' (nz _ hld) ((Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹)
    (mul_ne_zero (mul_ne_zero (nz _ hQ) (nz _ hS)) (inv_ne_zero hN'))
  refine ⟨(s.val : ℤ), (t.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hs : ((s.val : ℤ) : ZMod l) = s := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have ht : ((t.val : ℤ) : ZMod l) = t := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_pow, hs, ht]
  have hst' : s ^ 2 + (b : ZMod l) * s * t + ((a : ℤ) : ZMod l) * (c : ZMod l) * t ^ 2
      = (Q0 : ZMod l) * (S : ZMod l) * (N : ZMod l)⁻¹ := hst
  rw [hst', mul_assoc, inv_mul_cancel₀ hN', mul_one, sub_self]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_H_add_self (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (u v : m → ℂ) :
    stdH L m (u + v) (u + v) = stdH L m u u + stdH L m u v + stdH L m v u + stdH L m v v := by
  first
  | (simp only [map_add (f := _), LinearMap.add_apply]; ring)
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.add_apply, map_add (f := _), add_mul, mul_add,
      Finset.sum_add_distrib]; ring)

theorem rep_H_smul_left (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m (ξ • u) v = ξ * stdH L m u v := by
  first
  | (simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])

theorem rep_H_smul_right (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m v (ξ • u) = conj ξ * stdH L m v u := by
  first
  | (simp only [LinearMap.map_smulₛₗ, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum];
     refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring)

theorem rep_unit_vec (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (hld : ¬ (l : ℤ) ∣ d) :
    ∃ w : m → ℂ, SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ N S : ℤ, ¬ (l : ℤ) ∣ N ∧ ¬ (l : ℤ) ∣ S ∧
      stdH (cmL a b d ha hd lam hlam) m w w = repKappa a b d ha hd lam hlam * ((N : ℂ) / S) := by
  obtain ⟨xt, hxt, hxtT, yv, hyv, c₂, hc₂, hc₂l⟩ := rep_prim_pair a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set H := stdH L m with hHdef
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = repKappa a b d ha hd lam hlam := ⟨_, rfl⟩
  rw [← hκdef]
  set θ := cmTheta b d with hθdef
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  obtain ⟨mm, c₂', hmc, hc₂'⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt hyv
  rw [← hκdef] at hmc
  have hcc : c₂' = c₂ := by
    have : (c₂' : ℝ) = c₂ := by rw [← hc₂', hc₂]
    exact_mod_cast this
  rw [hcc] at hmc
  obtain ⟨m1, hm1⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt
  rw [← hκdef] at hm1
  have hy'sat := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ T hT hyv
  set yz := zT T yv with hyz
  have hyzT : ∀ j ∈ T, yz j = 0 := by intro j hj; simp [hyz, zT, hj]
  obtain ⟨n', hn', hn'y⟩ := hy'sat
  obtain ⟨m2, hm2⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hn'y
  rw [rep_H_nsmul, ← hκdef] at hm2
  have hn'0 : (n' : ℂ) ≠ 0 := by
    have : n' ≠ 0 := by rintro rfl; exact hn' (dvd_zero _)
    exact_mod_cast this
  have hS : ¬ (l : ℤ) ∣ (n' : ℤ) ^ 2 := fun h => hn' (by exact_mod_cast hlp.dvd_of_dvd_pow h)
  have hyy : H yz yz = κ * ((m2 : ℂ) / ((n' : ℤ) ^ 2 : ℤ)) := by
    push_cast; field_simp; linear_combination hm2
  have hκc : conj κ = κ := by
    rw [hκdef, rep_kappa_eq a b d ha hd lam hlam, map_div₀, Complex.conj_ofReal, map_ofNat]
  have hxy : H xt yz = κ * ((mm : ℂ) - c₂ * conj θ) := by rw [hHdef, rep_H_zT a b d ha hd lam hlam m T hxtT]; exact hmc
  have hyx : H yz xt = κ * ((mm : ℂ) - c₂ * θ) := by
    rw [hHdef, ← rep_H_conj, ← hHdef, hxy, map_mul, hκc, map_sub, map_mul, map_intCast, map_intCast,
      Complex.conj_conj]
  have e1 := rep_theta_add_conj b d
  have e2 := rep_theta_mul_conj a b c d hOK.1

  by_cases k1 : (l : ℤ) ∣ m1
  swap
  · refine ⟨xt, rep_sat_of_mem l Λ hxt hl, hxtT, m1 * n' ^ 2, n' ^ 2, ?_, hS, ?_⟩
    · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
      · exact k1 hh
      · exact hS hh
    · rw [hm1]; push_cast; field_simp
  by_cases k2 : (l : ℤ) ∣ m2
  swap
  · exact ⟨yz, ⟨n', hn', hn'y⟩, hyzT, m2, n' ^ 2, k2, hS, hyy⟩
  by_cases k3 : (l : ℤ) ∣ (m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2
  swap
  · refine ⟨xt + yz, rep_sat_add l Λ hl (rep_sat_of_mem l Λ hxt hl) ⟨n', hn', hn'y⟩, ?_, _, n' ^ 2, k3, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (-κ * c₂ * (n' : ℂ) ^ 2) * e1
  by_cases k4 : (l : ℤ) ∣ (a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2
  swap
  · refine ⟨θ • xt + yz, rep_sat_add l Λ hl (rep_sat_theta l Λ hθ (rep_sat_of_mem l Λ hxt hl)) ⟨n', hn', hn'y⟩,
      ?_, _, n' ^ 2, k4, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, rep_H_smul, rep_H_smul_left, rep_H_smul_right, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (κ * (n' : ℂ) ^ 2 * m1) * e2 + (κ * (n' : ℂ) ^ 2 * mm) * e1 -
        (2 * κ * (n' : ℂ) ^ 2 * c₂) * e2
  exfalso
  have d3 : (l : ℤ) ∣ (2 * mm - c₂ * b) * n' ^ 2 := by
    have e : (2 * mm - c₂ * b) * (n' : ℤ) ^ 2 = ((m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2) - m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k3 (Dvd.dvd.mul_right k1 _)) k2
  have d4 : (l : ℤ) ∣ (mm * b - 2 * a * c * c₂) * n' ^ 2 := by
    have e : (mm * b - 2 * a * c * c₂) * (n' : ℤ) ^ 2 =
        ((a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2) - (a * c) * m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k4 (Dvd.dvd.mul_right (Dvd.dvd.mul_left k1 _) _)) k2
  have d3' : (l : ℤ) ∣ 2 * mm - c₂ * b := (hlp.dvd_mul.mp d3).resolve_right hS
  have d4' : (l : ℤ) ∣ mm * b - 2 * a * c * c₂ := (hlp.dvd_mul.mp d4).resolve_right hS
  have d5 : (l : ℤ) ∣ c₂ * d := by
    have e : c₂ * (d : ℤ) = b * (2 * mm - c₂ * b) - 2 * (mm * b - 2 * a * c * c₂) := by
      linear_combination (-c₂) * hOK.1
    rw [e]; exact dvd_sub (Dvd.dvd.mul_left d3' b) (Dvd.dvd.mul_left d4' 2)
  rcases hlp.dvd_mul.mp d5 with h5 | h5
  · exact hc₂l h5
  · exact hld h5

theorem keyStart_of_ram (hR : KeyStartRam) : KeyStart := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h
  by_cases hld : l = d
  · exact hR a b c d ha hd lam hlam m Λ l x y T i₀ h hld
  have hOK := h.1
  have hl := h.2.2.2.2.2.1
  have hQ := h.2.2.2.2.2.2.1
  have hθ := h.2.2.1
  have hld' : ¬ (l : ℤ) ∣ d := by
    intro hh
    have : l ∣ d := by exact_mod_cast hh
    exact hld ((Nat.prime_dvd_prime_iff_eq hl hOK.2.2.2).mp this)
  obtain ⟨w, hw, hwT, N, S, hN, hS, hH⟩ := rep_unit_vec a b c d ha hd lam hlam m Λ l x y T i₀ h hld'
  obtain ⟨s, t, p, hp⟩ := rep_rep_modl hl a b c d hOK.1 hld' N S _ hN hS hQ
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  refine ⟨((s : ℂ) + t * cmTheta b d) • w, ?_, ?_, p, (a * x ^ 2 + b * x * y + c * y ^ 2) * S, ?_, ?_⟩
  · rw [add_smul, ← smul_smul]
    exact rep_sat_add l Λ hl (rep_sat_zsmul l Λ hw s) (rep_sat_zsmul l Λ (rep_sat_theta l Λ hθ hw) t)
  · intro j hj; simp [hwT j hj]
  · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
    · exact hQ hh
    · exact hS hh
  · have hS0 : (S : ℂ) ≠ 0 := by
      have : S ≠ 0 := by rintro rfl; exact hS (dvd_zero _)
      exact_mod_cast this
    obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : ℤ, Q0 = a * x ^ 2 + b * x * y + c * y ^ 2 := ⟨_, rfl⟩
    rw [← hQ0def] at hp hQ ⊢
    have hQ0 : (Q0 : ℂ) ≠ 0 := by
      have : Q0 ≠ 0 := by rintro rfl; exact hQ (dvd_zero _)
      exact_mod_cast this
    have hf' : stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
        repKappa a b d ha hd lam hlam * (Q0 : ℂ) := by
      rw [rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀, hQ0def]
    have e1 := rep_theta_add_conj b d
    have e2 := rep_theta_mul_conj a b c d hOK.1
    have hX : ((s : ℂ) + t * cmTheta b d) * conj ((s : ℂ) + t * cmTheta b d) =
        ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) := by
      simp only [map_add (f := _), map_mul, map_intCast]; push_cast
      linear_combination ((s : ℂ) * t) * e1 + (t : ℂ) ^ 2 * e2
    have hpC : (l : ℂ) ^ 1 * (p : ℂ) = ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) * N - (Q0 : ℂ) * S := by
      rw [pow_one]; exact_mod_cast hp.symm
    rw [rep_H_smul, hX, hH, hf', hpC]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
