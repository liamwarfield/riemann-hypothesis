module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.IsUnitOfNotMem
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def mI (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    calc v (algebraMap R C c) * v (algebraMap R C x) ≤ 1 * v (algebraMap R C x) :=
          mul_le_mul_of_nonneg_right (hv.map_le_one c) zero_le
      _ < 1 := by rwa [one_mul]

theorem mem_mI (hv : v.Integers R) (r : R) : r ∈ mI hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem v_eq_one_iff (hv : v.Integers R) (r : R) : v (algebraMap R C r) = 1 ↔ r ∉ mI hv := by
  rw [mem_mI, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (hv.map_le_one r) h⟩

theorem isUnit_of_not_mem (hv : v.Integers R) {r : R} (h : r ∉ mI hv) : IsUnit r :=
  hv.isUnit_of_one' ((v_eq_one_iff hv r).2 h)

theorem mI_isMaximal (hv : v.Integers R) : (mI hv).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_mI], fun J x hle hx hxJ => ?_⟩
  obtain ⟨u, rfl⟩ := isUnit_of_not_mem hv hx
  have : (↑u⁻¹ : R) * u ∈ J := J.mul_mem_left _ hxJ
  simpa using this

theorem isDomain (hv : v.Integers R) : IsDomain R := by
  have : Nontrivial R := ⟨0, 1, fun h => by
    have := congrArg (fun r => v (algebraMap R C r)) h
    simp at this⟩
  exact hv.hom_inj.isDomain (algebraMap R C)

abbrev res (hv : v.Integers R) : R →+* R ⧸ mI hv := Ideal.Quotient.mk (mI hv)

theorem res_eq_zero (hv : v.Integers R) (r : R) : res hv r = 0 ↔ v (algebraMap R C r) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

theorem res_ne_zero (hv : v.Integers R) (r : R) : res hv r ≠ 0 ↔ v (algebraMap R C r) = 1 := by
  rw [Ne, res_eq_zero, v_eq_one_iff hv, mem_mI]

instance instField (hv : v.Integers R) : Field (R ⧸ mI hv) :=
  haveI := mI_isMaximal hv
  Ideal.Quotient.field _

theorem charP (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1) : CharP (R ⧸ mI hv) p := by
  have h0 : ((p : R ⧸ mI hv)) = 0 := by
    rw [← map_natCast (res hv), res_eq_zero]; exact hpv
  exact (CharP.charP_iff_prime_eq_zero hp.out).2 h0

theorem idem_eq_zero (hv : v.Integers R) {n : Type} [Fintype n] [DecidableEq n]
    (e : Matrix n n R) (he : e * e = e) (hm : ∀ a b, e a b ∈ mI hv) : e = 0 := by
  have hmap : e.map (res hv) = 0 := by
    ext a b; simpa [Ideal.Quotient.eq_zero_iff_mem] using hm a b
  have hdet : IsUnit (1 - e).det := by
    apply isUnit_of_not_mem hv
    intro h
    have h1 : res hv (1 - e).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply, hmap, sub_zero,
      Matrix.det_one] at h1
    exact one_ne_zero h1
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  exact (hu.mul_left_eq_zero).1 this

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smul_cancel (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he (Matrix.ext hc)
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  have h2 := congrArg (algebraMap R C) h1
  rw [map_mul, map_mul] at h2
  have hne : algebraMap R C (e i j) ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap R C)] at h0
    exact hij (hv.hom_inj h0)
  exact hv.hom_inj (mul_right_cancel₀ hne h2)

theorem eig_pow_eq_one (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by
  have hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']
  have hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1 := by
    have := congrArg (algebraMap ℤ_[p] R).mapMatrix hN
    rwa [map_pow, map_one, RingHom.mapMatrix_apply] at this
  have h1 := hpow m
  rw [hN', one_mul] at h1
  exact (smul_cancel hv he (by rw [one_smul]; exact h1)).symm

theorem fermat (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] (z : ℤ_[p]) :
    res hv (algebraMap ℤ_[p] R z) ^ p = res hv (algebraMap ℤ_[p] R z) := by
  have hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hp0 : res hv (p : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hpv
  have h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0 := by
    rw [← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]
  rw [map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0

theorem proj (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [CommGroup G] [Fintype G] (hG : IsUnit (Fintype.card G : R))
    (A : G → Matrix n n ℤ_[p]) (hA : ∀ γ γ', A (γ * γ') = A γ * A γ') (hA1 : A 1 = 1)
    (εT : ι → Matrix n n R) (horth : ∀ i j, εT i * εT j = if i = j then εT i else 0)
    (hsum : ∑ i, εT i = 1) (ψ : ι → G → R)
    (heig : ∀ j γ, (A γ).map (algebraMap ℤ_[p] R) * εT j = ψ j γ • εT j)
    (hsep : ∀ j k, εT j ≠ 0 → εT k ≠ 0 → j ≠ k → ∃ γ, ψ j γ ≠ ψ k γ)
    (i : ι) (hi : εT i ≠ 0) : ∃ j, εT j ≠ 0 ∧ ∀ γ, ψ j γ = ψ i γ ^ p := by
  classical
  have hApow : ∀ γ (k : ℕ), A (γ ^ k) = A γ ^ k := by
    intro γ k
    induction k with
    | zero => simp [hA1]
    | succ k ih => rw [pow_succ, hA, ih, pow_succ]
  have hmul : ∀ j, εT j ≠ 0 → ∀ γ γ', ψ j (γ * γ') = ψ j γ * ψ j γ' := by
    intro j hj γ γ'
    apply smul_cancel hv hj
    have e1 := heig j (γ * γ')
    rw [hA, Matrix.map_mul, Matrix.mul_assoc, heig j γ', Matrix.mul_smul, heig j γ, smul_smul] at e1
    rw [← e1, mul_comm (ψ j γ')]
  have hn1 : 1 ≤ Fintype.card G := Fintype.card_pos
  have hpowG : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ Fintype.card G = 1 := fun j hj γ =>
    eig_pow_eq_one hv (A γ) (εT j) hj (ψ j γ) (heig j γ) (by rw [← hApow, pow_card_eq_one, hA1])
  have hiv : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ (Fintype.card G - 1) * ψ j γ = 1 := by
    intro j hj γ
    rw [← pow_succ, Nat.sub_add_cancel hn1, hpowG j hj γ]
  have hsum0 : ∀ χ : G → R, (∀ γ γ', χ (γ * γ') = χ γ * χ γ') → ∀ γ0, χ γ0 ≠ 1 →
      ∑ γ, χ γ = 0 := by
    intro χ hχ γ0 h0
    have e : ∑ γ, χ γ = χ γ0 * ∑ γ, χ γ := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_bijective (γ0 * ·) (Group.mulLeft_bijective γ0) (fun γ => χ γ0 * χ γ) χ
        (fun γ => (hχ γ0 γ).symm)).symm
    have e2 : (1 - χ γ0) * ∑ γ, χ γ = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    have e3 := congrArg (algebraMap R C) e2
    rw [map_mul, map_zero] at e3
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp (hv.hom_inj (h.trans (map_zero _).symm))).symm h0
    · exact hv.hom_inj (h.trans (map_zero _).symm)
  have hPe : ∀ (c : G → R) j, (∑ γ, c γ • (A γ).map (algebraMap ℤ_[p] R)) * εT j =
      (∑ γ, c γ * ψ j γ) • εT j := by
    intro c j
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.smul_mul, heig, smul_smul]
  have hdecomp : ∀ M : Matrix n n R, M = ∑ j, M * εT j := fun M => by
    rw [← Finset.mul_sum, hsum, Matrix.mul_one]
  by_contra hcon
  push_neg at hcon
  have hP'0 : (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) = 0 := by
    rw [hdecomp (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R))]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : εT j = 0
    · rw [hj, Matrix.mul_zero]
    · rw [hPe (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p) j]
      obtain ⟨γ0, hγ0⟩ := hcon j hj
      have hz := hsum0 (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p * ψ j γ)
        (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
          intro h1
          apply hγ0
          try simp only at h1
          calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) ^ p * ψ j γ0 := by
                rw [hiv i hi, one_pow, one_mul]
            _ = ((ψ i γ0 ^ (Fintype.card G - 1)) ^ p * ψ j γ0) * ψ i γ0 ^ p := by ring
            _ = ψ i γ0 ^ p := by rw [h1, one_mul])
      try simp only at hz
      rw [hz, zero_smul]
  have hPi : (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) =
      (Fintype.card G : R) • εT i := by
    rw [hdecomp (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)),
      Finset.sum_eq_single i]
    · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) i]
      simp only [hiv i hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · intro j _ hji
      by_cases hj : εT j = 0
      · rw [hj, Matrix.mul_zero]
      · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) j]
        obtain ⟨γ0, hγ0⟩ := hsep j i hj hi hji
        have hz := hsum0 (fun γ => ψ i γ ^ (Fintype.card G - 1) * ψ j γ)
          (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
            intro h1
            apply hγ0
            try simp only at h1
            calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) * ψ j γ0 := by
                  rw [hiv i hi, one_mul]
              _ = (ψ i γ0 ^ (Fintype.card G - 1) * ψ j γ0) * ψ i γ0 := by ring
              _ = ψ i γ0 := by rw [h1, one_mul])
        try simp only at hz
        rw [hz, zero_smul]
    · simp
  obtain ⟨a, b, hab⟩ : ∃ a b, εT i a b ∉ mI hv := by
    by_contra hc
    push_neg at hc
    exact hi (idem_eq_zero hv (εT i) (by rw [horth, if_pos rfl]) hc)
  haveI := charP p hv hpv
  have hfrob : res hv ((∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p •
      (A γ).map (algebraMap ℤ_[p] R)) a b) =
      res hv ((∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) a b) ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul,
      map_pow]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [mul_pow, fermat p hv hpv]
  have hres_n : res hv (Fintype.card G : R) ≠ 0 := by
    intro h0
    have h1 : IsUnit (res hv (Fintype.card G : R)) := hG.map (res hv)
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hres_e : res hv (εT i a b) ≠ 0 := by
    intro h0
    exact hab (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  rw [hP'0, hPi] at hfrob
  simp only [Matrix.zero_apply, map_zero, Matrix.smul_apply, smul_eq_mul, map_mul] at hfrob
  exact pow_ne_zero p (mul_ne_zero hres_n hres_e) hfrob.symm

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
