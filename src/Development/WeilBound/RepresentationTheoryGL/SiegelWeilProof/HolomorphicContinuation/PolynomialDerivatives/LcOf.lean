module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMomOfBasic
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStable
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreTop

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOfCore
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MomLin
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp [evX]
    ring
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [evX]
    ring

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HopPderivComm
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem hop_pderiv_comm' (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by
  have h : (⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_false (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, false) Q = -pderiv (a, i, false) Q + (2 * c : ℂ) • (X (a, i, true) * Q) := by
  simp [cr]

theorem cr_true (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, true) Q = -pderiv (a, i, true) Q + (2 * c : ℂ) • (X (a, i, false) * Q) := by
  simp [cr]

theorem hop_fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, support_C, if_neg hr, Finset.sum_singleton, coeff_C, if_pos rfl]
    simp [fockMono, smul_eq_C_mul]

theorem hop_pderiv_cr (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false]
    simp only [map_add (f := _), map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, false)]
    by_cases h : k = (a, i, true)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
  · rw [cr_true, cr_true]
    simp only [map_add (f := _), map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, true)]
    by_cases h : k = (a, i, false)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]

theorem sgn_mul_same (ε : Fin m → Bool) {a b : Fin m} (h : ε a = ε b) : sgn ε a * sgn ε b = 1 := by
  unfold sgn; rw [h]; split_ifs <;> norm_num

theorem sgn_mul_diff (ε : Fin m → Bool) {a b : Fin m} (h : ε a ≠ ε b) : sgn ε a * sgn ε b = -1 := by
  unfold sgn
  cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem hop_cr_C_mul (c : ℝ) (j : Fin m × Fin n × Bool) (r : ℂ) (Q : PX m n) : cr c j (C r * Q) = C r * cr c j Q := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
  · rw [cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring

section
variable (hB : FockBasic)
include hB

def hop_fL {c : ℝ} (hc : 0 < c) : PX m n →ₗ[ℂ] PX m n := IsLinearMap.mk' (fock c) (hB m n c hc).1

theorem fL_apply {c : ℝ} (hc : 0 < c) (p : PX m n) : hop_fL hB hc p = fock c p := rfl

theorem hop_fock_X_mul {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    fock c (X k * p) = cr c k (fock c p) := (hB m n c hc).2.2 k p

theorem fock_add'' {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q :=
  (hB m n c hc).1.map_add p q

theorem fock_zero' {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by
  rw [← fL_apply hB hc, map_zero]

theorem hop_deriv_fock {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (k.1, k.2.1, !k.2.2) (fock c p) = C (2 * c : ℂ) * fock c (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]
  | add p q hp hq =>
    rw [fock_add'' hB hc, map_add (f := _), hp, hq, map_add (f := _), fock_add'' hB hc, mul_add]
  | mul_X p j ih =>
    have hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0) := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
    have hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j := by
      obtain ⟨a, i, e⟩ := j
      obtain ⟨b, l, e'⟩ := k
      simp [Prod.ext_iff]
    rw [mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]
    by_cases h : k = j
    · rw [if_pos (hcond.2 h), if_pos h]; ring
    · rw [if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]; ring

theorem hop_tr_false {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, true) q
  have h2 := hop_deriv_fock hB hc (a, i, false) q
  rw [cr_true, smul_eq_C_mul] at h1
  simp only [Bool.not_false] at h2
  rw [h1, h2]; ring

theorem hop_tr_true {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, true) * fock c q) = fock c (X (a, i, false) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, true) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, false) q
  have h2 := hop_deriv_fock hB hc (a, i, true) q
  rw [cr_false, smul_eq_C_mul] at h1
  simp only [Bool.not_true] at h2
  rw [h1, h2]; ring

theorem fockHOp_of : FockHOp := by
  intro m n ε c hc a b p
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Y := fock c p with hY
  have d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p) := fun i => hop_deriv_fock hB hc (a, i, true) p
  have d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p) := fun i => hop_deriv_fock hB hc (b, i, false) p
  unfold hOp Dop
  rw [← fL_apply hB hc]
  by_cases h : ε a = ε b
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [if_pos h, map_sum, sgn_mul_same ε h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, fL_apply, fL_apply, d1, d2]
      have e1 := hop_tr_false hB hc b i (pderiv (a, i, true) p)
      have e2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
      rw [hop_pderiv_comm' (b, i, false) (a, i, true)] at e1
      simp only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]
      linear_combination e1 - e2
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [if_neg h, map_sum, sgn_mul_diff ε h]
      have hab : a ≠ b := fun e => h (e ▸ rfl)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]
      have t2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
      have t3 := hop_tr_true hB hc a i p
      have t4 := hop_tr_false hB hc b i (X (a, i, false) * p)
      have e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p := by
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
        have : ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false) := by simp [Ne.symm hab]
        simp [Pi.single_apply, this]
      rw [e5] at t4
      rw [hop_pderiv_comm' (a, i, true) (b, i, false)] at t2
      have e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p) := by
        congr 1; ring
      have hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1 := by
        rw [← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]
      have e7 : (c : ℂ) * (1 - -1) = 2 * c := by ring
      simp only [e7, map_neg, map_one, neg_one_mul, neg_neg]
      linear_combination t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 +
        (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK

end

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivComm
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.FK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def sw (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

theorem sw_inj {k k' : Fin m × Fin n × Bool} : sw k = sw k' ↔ k = k' := by
  obtain ⟨a, i, b⟩ := k
  obtain ⟨a', i', b'⟩ := k'
  cases b <;> cases b' <;> simp [sw]

theorem pderiv_comm (i j : Fin m × Fin n × Bool) (P : PX m n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅(pderiv (R := ℂ) i : Derivation ℂ (PX m n) (PX m n)), pderiv (R := ℂ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Pi.single_apply, hi, hj]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -(pderiv k Q) + (2 * c : ℂ) • ((X (sw k) : PX m n) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, sw]

theorem pderiv_cr (c : ℝ) (k k' : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv (sw k') (cr c k Q) = cr c k (pderiv (sw k') Q) + (if k = k' then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm (sw k') k]
  by_cases h : k = k'
  · subst h; simp; ring
  · have : sw k' ≠ sw k := fun e => h (sw_inj.1 e).symm
    simp [h, this]

theorem fock_one (c : ℝ) : fock c (1 : PX m n) = 1 := by
  classical
  have h1 : (1 : PX m n) = monomial 0 1 := rfl
  unfold fock
  rw [h1, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_smul]
  simp [fockMono]

theorem fock_C (hB : FockBasic) (c : ℝ) (hc : 0 < c) (a : ℂ) : fock c (C a : PX m n) = C a := by
  have hL := (hB m n c hc).1
  rw [show (C a : PX m n) = a • 1 by rw [smul_eq_C_mul, mul_one], hL.map_smul, fock_one, smul_eq_C_mul, mul_one]

theorem der_fock (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by
  classical
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  induction p using MvPolynomial.induction_on with
  | C a => rw [fock_C hB c hc]; simp [hL.map_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p k0 hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, ← hX, pderiv_mul, pderiv_X, hL.map_add (f := _), smul_add]
    by_cases h : k0 = k
    · subst h
      simp only [Pi.single_eq_same, if_true, mul_comm (X k0) (pderiv k0 p)]
      rw [one_mul, add_comm]
    · simp only [Pi.single_apply, h, if_false, add_zero, zero_smul, mul_comm (X k0) (pderiv k p)]
      rw [zero_mul, hL.map_zero, smul_zero, zero_add]

theorem qp_sum (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * ((X (a, i, true) : PX m n) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem op_id (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by
  classical
  have hd : (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P =
      ∑ a, (if i = j then (c : ℂ) * sgn ε a else 0) • P := by
    by_cases hij : i = j <;> simp [hij, Finset.mul_sum, Finset.sum_smul]
  rw [hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold mulQ lapS eulH eulA
  rw [qp_sum, Finset.sum_mul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hε : ε a
  · simp only [hε, Bool.false_eq_true, if_false, if_true, zero_sub, cr_apply, sw, Bool.not_true]
    rw [pderiv_comm (a, j, true) (a, i, false)]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
  · simp only [hε, if_true, Bool.true_eq_false, if_false, sub_zero, cr_apply, sw, Bool.not_false]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring

theorem kopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by
  simp [KopL]

end PositivityTheory.Rg.Sw.LC.FK

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK

theorem fockK_of (hB : FockBasic) : FockK := by
  intro m n ε c hc
  have hc2 : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  refine ⟨(2 * c : ℂ)⁻¹ * (c : ℂ) ^ 2, -(2 * c : ℂ)⁻¹, -((2 * c : ℂ)⁻¹ * c), (2 * c : ℂ)⁻¹ * c,
    -((2 * c : ℂ)⁻¹ * ((c : ℂ) * ∑ a, sgn ε a)), fun i j p => ?_⟩
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  let L : PX m n →ₗ[ℂ] PX m n := hL.mk' (fock c)
  have eL : ∀ x, fock c x = L x := fun x => rfl
  have hd : ∀ k (q : PX m n), fock c (pderiv k q) = (2 * c : ℂ)⁻¹ • pderiv (sw k) (fock c q) := by
    intro k q
    rw [der_fock hB c hc, inv_smul_smul₀ hc2]
  have key : fock c (KopL ε i j p) = (2 * c : ℂ)⁻¹ •
      ((∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) (fock c p))) -
        ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) (fock c p))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [kopL_apply, eL, map_sub, map_sum, map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
  rw [key, op_id]
  by_cases hij : i = j
  · simp only [hij, if_true]
    module
  · simp only [hij, if_false, zero_smul, sub_zero, add_zero]
    module

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MapDomainFlpFlp
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Basic

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool

def flp (k : Ix m n) : Ix m n := (k.1, k.2.1, !k.2.2)

theorem flp_flp (k : Ix m n) : flp (flp k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flp]

def flpEquiv : Ix m n ≃ Ix m n := ⟨flp, flp, flp_flp, flp_flp⟩

theorem flp_injective : Function.Injective (flp (m := m) (n := n)) := flpEquiv.injective

theorem cr_apply (c : ℝ) (k : Ix m n) (P : PX m n) :
    cr c k P = (2 * c : ℂ) • (X (flp k) * P) - pderiv k P := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> (simp [cr, flp]; try abel)

theorem pderiv_comm' (k l : Ix m n) (P : PX m n) :
    pderiv k (pderiv l P) = pderiv l (pderiv k P) := by
  classical
  have h : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv l : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simp only [Derivation.commutator_apply] at h2
  exact sub_eq_zero.mp (by simpa using h2)

theorem cr_comm (c : ℝ) (k l : Ix m n) (P : PX m n) :
    cr c k (cr c l P) = cr c l (cr c k P) := by
  classical
  simp only [cr_apply, map_sub, Derivation.map_smul, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul]
  simp only [MvPolynomial.smul_eq_C_mul, pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
  rw [pderiv_comm' k l P]
  have e : (flp l = k) ↔ (flp k = l) :=
    ⟨fun h => by rw [← h, flp_flp], fun h => by rw [← h, flp_flp]⟩
  by_cases h : flp l = k
  · have h' := e.mp h
    simp only [h, h', if_true]
    ring
  · have h' : ¬ flp k = l := fun h'' => h (e.mpr h'')
    simp only [h, h', if_false]
    ring

theorem crAlg_comm (c : ℝ) : ∀ a ∈ Set.range (cr (m := m) (n := n) c), ∀ b ∈ Set.range (cr (m := m) (n := n) c),
    a * b = b * a := by
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  exact LinearMap.ext fun P => cr_comm c k l P

abbrev CrAlg (m n : ℕ) (c : ℝ) : Subalgebra ℂ (Module.End ℂ (PX m n)) := Algebra.adjoin ℂ (Set.range (cr c))

instance instCommRingCrAlg (c : ℝ) : CommRing (CrAlg m n c) :=
  letI : IsMulCommutative (CrAlg m n c) :=
    Algebra.isMulCommutative_adjoin ℂ fun a ha b hb _ => crAlg_comm c a ha b hb
  { (CrAlg m n c).toRing with mul_comm := mul_comm' }

def gen (c : ℝ) (k : Ix m n) : CrAlg m n c := ⟨cr c k, Algebra.subset_adjoin ⟨k, rfl⟩⟩

def phi (c : ℝ) : PX m n →ₐ[ℂ] CrAlg m n c := MvPolynomial.aeval (gen c)

theorem coe_phi_monomial (c : ℝ) (s : Ix m n →₀ ℕ) :
    ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) =
      ((Finset.univ : Finset (Ix m n)).toList.map fun k => (cr c k) ^ (s k)).prod := by
  rw [phi, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_map_toList]
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  congr 1

theorem fockMono_eq (c : ℝ) (s : Ix m n →₀ ℕ) :
    fockMono c s = ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  rw [coe_phi_monomial]; rfl

theorem fock_eq (c : ℝ) (p : PX m n) : fock c p = ((phi c p : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply, fockMono_eq]

theorem fock_add (c : ℝ) (p q : PX m n) : fock c (p + q) = fock c p + fock c q := by
  simp only [fock_eq, map_add (f := _), Subalgebra.coe_add, LinearMap.add_apply]

theorem fock_smul (c : ℝ) (a : ℂ) (p : PX m n) : fock c (a • p) = a • fock c p := by
  simp only [fock_eq, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply]

theorem fock_zero (c : ℝ) : fock c (0 : PX m n) = 0 := by simp [fock]

theorem fock_sub (c : ℝ) (p q : PX m n) : fock c (p - q) = fock c p - fock c q := by
  have := fock_add c (p - q) q
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem fock_sum (c : ℝ) {ι : Type*} (t : Finset ι) (f : ι → PX m n) :
    fock c (∑ i ∈ t, f i) = ∑ i ∈ t, fock c (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add, ih]

theorem fock_X_mul (c : ℝ) (k : Ix m n) (p : PX m n) : fock c (X k * p) = cr c k (fock c p) := by
  rw [fock_eq, fock_eq, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
  simp [phi, gen]

theorem fock_monomial (c : ℝ) (s : Ix m n →₀ ℕ) : fock c (monomial s 1) = fockMono c s := by
  rw [fockMono_eq, fock_eq]

theorem degree_add' (a b : Ix m n →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]

theorem degree_mapDomain (t : Ix m n →₀ ℕ) : (Finsupp.mapDomain flp t).degree = t.degree := by
  simp only [Finsupp.degree_eq_sum]
  rw [← Equiv.sum_comp flpEquiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.mapDomain_apply_of_injective flp_injective t i

theorem mapDomain_flp_flp (t : Ix m n →₀ ℕ) : Finsupp.mapDomain flp (Finsupp.mapDomain flp t) = t := by
  rw [← Finsupp.mapDomain_comp]
  have : (flp ∘ flp : Ix m n → Ix m n) = id := funext flp_flp
  rw [this, Finsupp.mapDomain_id]

def DegLT (d : ℕ) (Q : PX m n) : Prop := ∀ t ∈ Q.support, t.degree < d

theorem DegLT.zero (d : ℕ) : DegLT d (0 : PX m n) := by simp [DegLT]

theorem DegLT.add {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P + Q) := by
  classical
  intro t ht
  rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
  · exact hP t h
  · exact hQ t h

theorem DegLT.neg {d : ℕ} {P : PX m n} (hP : DegLT d P) : DegLT d (-P) := by
  intro t ht; rw [MvPolynomial.support_neg] at ht; exact hP t ht

theorem DegLT.sub {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

theorem DegLT.smul {d : ℕ} {P : PX m n} (a : ℂ) (hP : DegLT d P) : DegLT d (a • P) := by
  intro t ht; exact hP t (MvPolynomial.support_smul ht)

theorem DegLT.mono {d d' : ℕ} {P : PX m n} (hP : DegLT d P) (h : d ≤ d') : DegLT d' P :=
  fun t ht => lt_of_lt_of_le (hP t ht) h

theorem DegLT.sum {d : ℕ} {ι : Type*} (t : Finset ι) (f : ι → PX m n) (h : ∀ i ∈ t, DegLT d (f i)) :
    DegLT d (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using DegLT.zero d
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DegLT.X_mul {d : ℕ} {P : PX m n} (j : Ix m n) (hP : DegLT d P) : DegLT (d + 1) (X j * P) := by
  intro t ht
  rw [MvPolynomial.support_X_mul] at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
  simp only [addLeftEmbedding_apply, degree_add', Finsupp.degree_single]
  have := hP t' ht'
  omega

theorem DegLT.pderiv {d : ℕ} {P : PX m n} (k : Ix m n) (hP : DegLT d P) : DegLT d (pderiv k P) := by
  classical
  intro t ht
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum] at ht
  obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
  rw [pderiv_monomial] at hts
  have ht' := MvPolynomial.support_monomial_subset hts
  rw [Finset.mem_singleton] at ht'
  subst ht'
  refine lt_of_le_of_lt ?_ (hP s hs)
  simp only [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun i _ => tsub_le_self

def Sm (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := monomial (Finsupp.mapDomain flp s) ((2 * c : ℂ) ^ s.degree)

def err (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := fockMono c s - Sm c s

theorem Sm_succ (c : ℝ) (s : Ix m n →₀ ℕ) (k : Ix m n) :
    Sm c (s + Finsupp.single k 1) = (2 * c : ℂ) • (X (flp k) * Sm c s) := by
  simp only [Sm, Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_add', Finsupp.degree_single, pow_succ]
  rw [add_comm (Finsupp.mapDomain flp s), monomial_single_add, pow_one, ← mul_smul_comm, smul_monomial, smul_eq_mul,
    mul_comm (2 * (c : ℂ))]

theorem Sm_deg (c : ℝ) (s : Ix m n →₀ ℕ) : DegLT (s.degree + 1) (Sm c s) := by
  intro t ht
  have := MvPolynomial.support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  subst this
  rw [degree_mapDomain]
  omega

theorem fockMono_zero (c : ℝ) : fockMono (m := m) (n := n) c 0 = 1 := by
  simp [fockMono]

theorem err_deg (c : ℝ) : ∀ d : ℕ, ∀ s : Ix m n →₀ ℕ, s.degree = d → DegLT d (err c s) := by
  intro d
  induction d with
  | zero =>
    intro s hs
    have : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst this
    simp [err, Sm, fockMono_zero, DegLT.zero]
  | succ d ih =>
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h; subst h; simp at hs
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
      by_contra h; push_neg at h; exact hs0 (Finsupp.ext h)
    have hle : Finsupp.single k 1 ≤ s := by
      intro i
      by_cases hi : i = k
      · subst hi; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    set s' := s - Finsupp.single k 1 with hs'
    have hsplit : s = s' + Finsupp.single k 1 := (tsub_add_cancel_of_le hle).symm
    have hd' : s'.degree = d := by
      have := degree_add' s' (Finsupp.single k 1)
      rw [← hsplit, Finsupp.degree_single] at this
      omega
    have hrec : fockMono c s = cr c k (fockMono c s') := by
      rw [← fock_monomial, ← fock_monomial, hsplit, add_comm, monomial_single_add, pow_one, fock_X_mul]
    have e : err c s = (2 * c : ℂ) • (X (flp k) * err c s') - pderiv k (Sm c s' + err c s') := by
      rw [err, hrec, cr_apply, hsplit, Sm_succ, err]
      simp only [sub_add_cancel, mul_sub, smul_sub]
      abel
    rw [e]
    refine DegLT.sub (DegLT.smul _ (DegLT.X_mul _ (ih s' hd'))) (DegLT.pderiv _ (DegLT.add ?_ ((ih s' hd').mono (by omega))))
    have := Sm_deg c s'
    rwa [hd'] at this

theorem fock_decomp (c : ℝ) (p : PX m n) :
    fock c p = ∑ s ∈ p.support, p.coeff s • (Sm c s + err c s) := by
  simp only [fock, err, add_sub_cancel]

theorem fock_injective (c : ℝ) (hc : 0 < c) : Function.Injective (fock (m := m) (n := n) c) := by
  classical
  intro p q hpq
  rw [← sub_eq_zero]
  have h0 : fock c (p - q) = 0 := by rw [fock_sub, hpq, sub_self]
  set r := p - q
  by_contra hr
  have hne : r.support.Nonempty := MvPolynomial.support_nonempty.mpr hr
  obtain ⟨s0, hs0, hmax⟩ := Finset.exists_max_image r.support Finsupp.degree hne
  have key := congrArg (AddMonoidAlgebra.coeff · (Finsupp.mapDomain flp s0)) h0
  rw [fock_decomp, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single s0] at key
  · rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial, if_pos rfl] at key
    have herr : AddMonoidAlgebra.coeff (err c s0) (Finsupp.mapDomain flp s0) = 0 := by
      by_contra hne'
      have := err_deg c _ s0 rfl _ (MvPolynomial.mem_support_iff.mpr hne')
      rw [degree_mapDomain] at this
      exact lt_irrefl _ this
    rw [herr, add_zero, smul_eq_mul] at key
    have hc' : (2 * c : ℂ) ≠ 0 := by
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      exact mul_ne_zero two_ne_zero this
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hs0) (pow_ne_zero _ hc')) key
  · intro s hs hne'
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial]
    have h1 : Finsupp.mapDomain flp s ≠ Finsupp.mapDomain flp s0 :=
      fun h => hne' (Finsupp.mapDomain_injective flp_injective h)
    rw [if_neg h1]
    have herr : AddMonoidAlgebra.coeff (err c s) (Finsupp.mapDomain flp s0) = 0 := by
      by_contra hne''
      have := err_deg c _ s rfl _ (MvPolynomial.mem_support_iff.mpr hne'')
      rw [degree_mapDomain] at this
      exact absurd (hmax s hs) (not_le.mpr this)
    rw [herr, add_zero, smul_zero]
  · intro h; exact absurd hs0 h

theorem fock_surj_deg (c : ℝ) (hc : 0 < c) :
    ∀ d : ℕ, ∀ Q : PX m n, DegLT d Q → ∃ p, fock c p = Q := by
  classical
  have hc' : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  intro d
  induction d with
  | zero =>
    intro Q hQ
    refine ⟨0, ?_⟩
    rw [fock_zero]
    symm
    by_contra hne
    obtain ⟨t, ht⟩ := MvPolynomial.support_nonempty.mpr hne
    exact Nat.not_lt_zero _ (hQ t ht)
  | succ d ih =>
    intro Q hQ
    set p0 : PX m n := ∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • monomial (Finsupp.mapDomain flp t) 1
    have hp0 : fock c p0 = (∑ t ∈ Q.support, monomial t (Q.coeff t)) + ∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t) := by
      rw [fock_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [fock_smul, fock_monomial, err, smul_sub, Sm, mapDomain_flp_flp, degree_mapDomain, smul_monomial,
        smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc')]
      abel
    have hR : DegLT d (∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t)) := by
      refine DegLT.sum _ _ fun t ht => DegLT.smul _ ?_
      have h1 := err_deg c _ (Finsupp.mapDomain flp t) rfl
      rw [degree_mapDomain] at h1
      exact h1.mono (by have := hQ t ht; omega)
    obtain ⟨p1, hp1⟩ := ih _ hR
    exact ⟨p0 - p1, by rw [fock_sub, hp0, hp1, add_sub_cancel_right]; exact Q.as_sum.symm⟩

theorem fock_surjective (c : ℝ) (hc : 0 < c) : Function.Surjective (fock (m := m) (n := n) c) := by
  intro Q
  refine fock_surj_deg c hc (Q.support.sup Finsupp.degree + 1) Q fun t ht => ?_
  exact Nat.lt_succ_of_le (Finset.le_sup ht)

theorem fockBasic : FockBasic := by
  intro m n c hc
  exact ⟨⟨fock_add c, fun a p => fock_smul c a p⟩, ⟨fock_injective c hc, fock_surjective c hc⟩, fun k p => fock_X_mul c k p⟩

end PositivityTheory.Rg.Sw.LC.Basic

namespace PositivityTheory.Rg.Sw.LC

theorem fockBasic : FockBasic := Basic.fockBasic

end PositivityTheory.Rg.Sw.LC
end
end

namespace PositivityTheory.Rg.Sw.LC

private theorem nullSec_add' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P Q : PX m n}
    (hP : NullSec ε c P) (hQ : NullSec ε c Q) : NullSec ε c (P + Q) := by
  intro R hR
  rw [mul_add, (momLin m n c hc (R * P) (R * Q) 1).1, hP R hR, hQ R hR, add_zero]

private theorem nullSec_smul' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P : PX m n}
    (r : ℂ) (hP : NullSec ε c P) : NullSec ε c (r • P) := by
  intro R hR
  rw [mul_smul_comm, (momLin m n c hc (R * P) 0 r).2, hP R hR, mul_zero]

private theorem nullSec_fock_apply_of_mem_kAlg {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c)
    (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) :
    ∀ p : PX m n, NullSec ε c (fock c p) → NullSec ε c (fock c (w p)) := by
  have hlin := (fockBasic m n c hc).1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, hk⟩ := fockK_of fockBasic m n ε c hc
  have hN := nullStable m n ε c hc
  have hw' : w ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2) := hw
  clear hw
  induction hw' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    intro p hp
    show NullSec ε c (fock c (KopL ε i j p))
    rw [hk i j p]
    obtain ⟨h1, h2, h3, h4⟩ := hN i j _ hp
    exact nullSec_add' hc (nullSec_add' hc (nullSec_add' hc (nullSec_add' hc
      (nullSec_smul' hc _ h4) (nullSec_smul' hc _ h1)) (nullSec_smul' hc _ h2))
      (nullSec_smul' hc _ h3)) (nullSec_smul' hc _ hp)
  | algebraMap r =>
    intro p hp
    rw [Module.algebraMap_end_apply, hlin.map_smul]
    exact nullSec_smul' hc r hp
  | add x y _ _ hx hy =>
    intro p hp
    rw [LinearMap.add_apply, hlin.map_add (f := _)]
    exact nullSec_add' hc (hx p hp) (hy p hp)
  | mul x y _ _ hx hy =>
    intro p hp
    exact hx _ (hy p hp)

theorem lc_of_core (hC : CoreLC) : PositivityTheory.Rg.Sw.LC := by
  intro m n ε c hc lam hlam P hP
  obtain ⟨hlin, hbij, -⟩ := fockBasic m n c hc
  let F : PX m n →ₗ[ℂ] PX m n := hlin.mk' _
  let Λ : PX m n →ₗ[ℂ] ℂ := lam.comp F
  have hΛ : ∀ (a b : Fin m) (p : PX m n), Λ (Dop ε c a b p) = 0 := by
    intro a b p
    show lam (fock c (Dop ε c a b p)) = 0
    rw [← fockHOp_of fockBasic m n ε c hc a b p]
    exact hlam a b _
  obtain ⟨p, rfl⟩ := hbij.2 P
  obtain ⟨w, hw, hval⟩ := hC m n ε c hc Λ hΛ p
  have h1 : lam (fock c p) = contr c (w p) := hval
  rw [h1]
  have hM := fockMom_of_basic fockBasic m n c hc
  have h0 : mom c (fock c (w p)) = 0 := by
    simpa using nullSec_fock_apply_of_mem_kAlg hc w hw p hP 1 (Subalgebra.one_mem _)
  rw [hM.2] at h0
  exact (mul_eq_zero.mp h0).resolve_left hM.1

end PositivityTheory.Rg.Sw.LC
end

namespace PositivityTheory.Rg.Sw

theorem lc_of (h : FFT) : LC := LC.lc_of_core (LC.coreLC_of h)

end PositivityTheory.Rg.Sw
