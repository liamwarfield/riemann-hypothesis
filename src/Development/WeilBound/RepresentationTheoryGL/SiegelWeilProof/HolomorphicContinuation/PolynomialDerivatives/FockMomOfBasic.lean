module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.OneMom
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

def OneMom : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ p q : ℕ,
    MeasureTheory.Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) ∧
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContrEqOfSubset
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.GaussianMomentRecurrence
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableMonomial
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def flip (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

@[simp] theorem flip_flip (k : Fin m × Fin n × Bool) : flip (flip k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flip]

def g1 (c : ℝ) (p q : ℕ) : ℂ := if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

def phi (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, g1 c (s (a, i, false)) (s (a, i, true))

def fac (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) (z : ℂ) : ℂ :=
  z ^ s (a, i, false) * star z ^ s (a, i, true) * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))

theorem evX_monomial_mul_gs (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) (x : Fin m → Fin n → ℂ) :
    evX (monomial s r) x * gs c x = r * ∏ a, ∏ i, fac c s a i (x a i) := by
  have h1 : evX (monomial s r) x = r * ∏ a, ∏ i, (x a i ^ s (a, i, false) * star (x a i) ^ s (a, i, true)) := by
    rw [evX, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.prod_bool]
    simp [mul_comm]
  have h2 : gs c x = ∏ a, ∏ i, Complex.exp ((-(c * ‖x a i‖ ^ 2) : ℝ)) := by
    rw [gs, ← Complex.ofReal_neg]
    have : (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℝ) = ∑ a, ∑ i, (-(c * ‖x a i‖ ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [this, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Complex.ofReal_sum, Complex.exp_sum]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext a
  rw [← Finset.prod_mul_distrib]
  rfl

variable (hM : OneMom)

include hM in
theorem integrable_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX (monomial s r) x * gs c x) := by
  simp_rw [evX_monomial_mul_gs]
  refine Integrable.const_mul ?_ r
  exact Integrable.fintype_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))
    (fun a => Integrable.fintype_prod (f := fun i (z : ℂ) => fac c s a i z) (fun i => (hM c hc _ _).1))

include hM in
theorem mom_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    mom c (monomial s r) = r * phi c s := by
  rw [mom]
  simp_rw [evX_monomial_mul_gs]
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_volume_eq_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) => fac c s a i z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hM c hc _ _).2

include hM in
theorem integrable_evX (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r => exact integrable_monomial hM c hc s r
  | add P Q hP hQ =>
    have : (fun x => evX (P + Q) x * gs c x) = fun x => evX P x * gs c x + evX Q x * gs c x := by
      funext x; simp [evX, add_mul]
    rw [this]; exact hP.add hQ

include hM in
theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  rw [mom, mom, mom, ← integral_add (integrable_evX hM c hc P) (integrable_evX hM c hc Q)]
  congr 1; funext x; simp [evX, add_mul]

omit hM in
theorem mom_smul (c : ℝ) (r : ℂ) (P : PX m n) : mom c (r • P) = r * mom c P := by
  rw [mom, mom, ← integral_const_mul]
  congr 1; funext x; simp [evX, mul_assoc]

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gaussian_moment_symm (c : ℝ) (p q : ℕ) : g1 c p q = g1 c q p := by
  unfold g1; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem gaussian_moment_recurrence (c : ℝ) (hc : 0 < c) (p q : ℕ) : (p : ℂ) * g1 c (p - 1) q = (c : ℂ) * g1 c p (q + 1) := by
  rcases p with _ | p
  · simp [g1]
  · simp only [Nat.add_sub_cancel, g1, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp

theorem phi_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    phi c s = g1 c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold phi
  rw [← Fintype.prod_prod_type' (f := fun a i => g1 c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem rest_congr (c : ℝ) (s s' : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n)
    (h : ∀ x : Fin m × Fin n, x ≠ (a, i) → ∀ b, s (x.1, x.2, b) = s' (x.1, x.2, b)) :
    ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s' (x.1, x.2, false)) (s' (x.1, x.2, true)) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_erase.1 hx).1
  rw [h x hx' false, h x hx' true]

theorem phi_rel (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _

variable (hM : OneMom)


include hM in
theorem mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add (f := _), mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]

theorem pderiv_comm (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (pderiv j Q) = pderiv j (pderiv k Q) := by
  have : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv j : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    classical
    rw [pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D Q) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.1 h

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -pderiv k Q + (2 * c : ℂ) • (X (flip k) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, flip]

theorem pderiv_cr (c : ℝ) (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + (if k = flip j then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm k j]
  by_cases h : k = flip j
  · subst h; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, h, Ne.symm h]

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hC (c : ℝ) (p q : ℕ) : ℂ := if p = q then (p.factorial : ℂ) * (2 * c : ℂ) ^ p else 0

def wC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))

theorem hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by
  unfold hC; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hC_rel (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp

theorem contr_eq (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp

theorem contr_eq_of_subset (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_monomial (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) : contr c (monomial s r) = r * wC c s := by
  classical
  rw [contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem contr_C (c : ℝ) (r : ℂ) : contr c (C r : PX m n) = r := by
  rw [← monomial_zero', contr_monomial]
  simp [wC, hC]

theorem wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold wC
  rw [← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem wC_rel (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _

theorem contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]
    ring
  | add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add (f := _), contr_add, mul_add]

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableRpowGauss
noncomputable section

open MeasureTheory Set Real

namespace PositivityTheory.Rg.Sw.LC.Mom1

theorem norm_integrand (c : ℝ) (p q : ℕ) (z : ℂ) :
    ‖z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))‖ =
      ‖z‖ ^ ((p + q : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_star, Complex.norm_exp_ofReal, Real.rpow_natCast,
    Real.rpow_two, pow_add]
  ring_nf

theorem integrable_rpow_gauss (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun z : ℂ => ‖z‖ ^ s * Real.exp (-c * ‖z‖ ^ (2 : ℝ))) := by
  by_contra h
  have h1 := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s) (b := c) (by norm_num)
    (by linarith) hc
  rw [integral_undef h] at h1
  have hG := Real.Gamma_pos_of_pos (s := (s + 2) / 2) (by linarith)
  have : 0 < (2 * π / 2) * c ^ (-(s + 2) / 2) * Real.Gamma ((s + 2) / 2) := by
    have := Real.pi_pos
    positivity
  linarith

theorem continuous_integrand (c : ℝ) (p q : ℕ) :
    Continuous (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  ((continuous_pow p).mul (continuous_star.pow q)).mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
      ((continuous_const.mul (continuous_norm.pow 2)).neg)))

theorem integrable_integrand (c : ℝ) (hc : 0 < c) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  (integrable_rpow_gauss c hc ((p + q : ℕ) : ℝ) (by positivity)).mono'
    (continuous_integrand c p q).aestronglyMeasurable
    (ae_of_all _ fun z => (norm_integrand c p q z).le)

theorem integral_diag (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) := by
  have e : ∀ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((‖z‖ ^ ((2 * p : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) : ℝ) : ℂ) := by
    intro z
    rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Real.rpow_natCast,
      Real.rpow_two]
    push_cast
    rw [pow_mul]
    ring_nf
  simp_rw [e]
  rw [integral_complex_ofReal, Complex.integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by have : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by positivity
        linarith) hc]
  congr 1
  have h1 : ((((2 * p : ℕ) : ℝ) + 2) / 2) = (p : ℝ) + 1 := by push_cast; ring
  rw [h1, show (-(((2 * p : ℕ) : ℝ) + 2) / 2) = -((p : ℝ) + 1) by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg hc.le, show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  field_simp

theorem integral_offdiag (c : ℝ) (p q : ℕ) (hpq : p ≠ q) :
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) = 0 := by
  set F : ℂ → ℂ := fun z => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) with hF
  set f : ℝ → ℂ := fun r => (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) with hf
  set k : ℂ := ((p : ℂ) - q) * Complex.I with hk
  set g : ℝ → ℂ := fun θ => Complex.exp (k * θ) with hg
  have hk0 : k ≠ 0 := by
    rw [hk]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [sub_ne_zero]
    exact_mod_cast hpq
  have hpt : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π, x.1 • F (Complex.polarCoord.symm x) = f x.1 * g x.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    have he : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I = Complex.exp (θ * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp only [hF, hf, hg, hk]
    rw [hn, Complex.polarCoord_symm_apply]
    simp only
    rw [he, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hc : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [hc]
    have : Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I)) =
        Complex.exp (((p : ℂ) - q) * Complex.I * θ) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc (r : ℂ) * ((r : ℂ) ^ p * Complex.exp (↑p * (↑θ * Complex.I)) *
            ((r : ℂ) ^ q * Complex.exp (↑q * -(↑θ * Complex.I))) * Complex.exp ((-(c * r ^ 2) : ℝ)))
        = (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) *
            (Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I))) := by ring
      _ = _ := by rw [this]
  have hgI : ∫ θ in Ioo (-π) π, g θ = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      hg]
    simp only
    rw [integral_exp_mul_complex hk0]
    have : k * (π : ℂ) = k * ((-π : ℝ) : ℂ) + (((p : ℤ) - q : ℤ) : ℂ) * (2 * π * Complex.I) := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]
  rw [← Complex.integral_comp_polarCoord_symm F, polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt, Measure.volume_eq_prod,
    setIntegral_prod_mul f g, hgI, mul_zero]

theorem oneMom : OneMom := by
  intro c hc p q
  refine ⟨integrable_integrand c hc p q, ?_⟩
  split_ifs with h
  · subst h; exact integral_diag c hc p
  · exact integral_offdiag c p q h

end PositivityTheory.Rg.Sw.LC.Mom1

namespace PositivityTheory.Rg.Sw.LC

theorem oneMom : OneMom := Mom1.oneMom

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem fockMono_zero (c : ℝ) : fockMono c (0 : Fin m × Fin n × Bool →₀ ℕ) = (1 : PX m n) := by
  simp [fockMono]

theorem fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, ← monomial_zero', support_monomial, if_neg hr, Finset.sum_singleton, coeff_monomial, if_pos rfl,
      fockMono_zero, smul_eq_C_mul, mul_one, monomial_zero']

theorem deg_lt (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) (hk : s k ≠ 0)
    (t : Fin m × Fin n × Bool →₀ ℕ) (ht : ∀ x, t x ≤ (s - Finsupp.single k 1 : Fin m × Fin n × Bool →₀ ℕ) x) : ∑ x, t x < ∑ x, s x := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ => ht x) ?_
  refine Finset.sum_lt_sum (fun x _ => by simp) ⟨k, Finset.mem_univ _, ?_⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

variable (hB : FockBasic)

include hB in
theorem pderiv_fock (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv k (fock c p) = (2 * c : ℂ) • fock c (pderiv (flip k) p) := by
  classical
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  induction p using MvPolynomial.induction_on with
  | C r => rw [fock_C, pderiv_C, pderiv_C, hL.map_zero, smul_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, pderiv_mul, pderiv_X, hL.map_add (f := _), hX, Pi.single_apply]
    by_cases h : k = flip j
    · have h' : j = flip k := by rw [h, flip_flip]
      rw [if_pos h, if_pos h', one_mul, smul_add, add_comm]
    · have h' : ¬ j = flip k := fun e => h (by rw [e, flip_flip])
      rw [if_neg h, if_neg h', zero_mul, hL.map_zero, zero_smul, add_zero, zero_add]

variable (hM : OneMom)

include hB hM in
theorem mom_fock_X (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  have e1 := mom_pderiv hM c hc k (fock c p)
  have e2 : mom c (pderiv k (fock c p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
    rw [pderiv_fock hB c hc, mom_smul]
  rw [hX, cr_apply, mom_add hM c hc, ← neg_one_smul ℂ (pderiv k (fock c p)), mom_smul, mom_smul, ← e2, e1]
  ring

include hB hM in
theorem fockMom_of : FockMom := by
  intro m n c hc
  obtain ⟨hL, -, -⟩ := hB m n c hc
  have h1 : mom c (1 : PX m n) ≠ 0 := by
    rw [← C_1, ← monomial_zero', mom_monomial hM c hc, one_mul, phi]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [Finsupp.coe_zero, Pi.zero_apply, g1, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
      pow_one, if_true]
    exact_mod_cast (div_pos Real.pi_pos hc).ne'
  refine ⟨h1, ?_⟩
  let D : PX m n → ℂ := fun p => mom c (fock c p) - mom c (1 : PX m n) * contr c p
  have hDadd : ∀ p q, D (p + q) = D p + D q := by
    intro p q; simp only [D]; rw [hL.map_add (f := _), mom_add hM c hc, contr_add]; ring
  have hDC : ∀ r, D (C r) = 0 := by
    intro r; simp only [D]
    rw [fock_C, contr_C, C_eq_smul_one, mom_smul]; ring
  have hDX : ∀ k p, D (X k * p) = (2 * c : ℂ) * D (pderiv (flip k) p) := by
    intro k p; simp only [D]; rw [mom_fock_X hB hM c hc, contr_X_mul]; ring
  have hmono : ∀ N, ∀ s : Fin m × Fin n × Bool →₀ ℕ, ∑ x, s x = N → ∀ r, D (monomial s r) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro s hs r
      by_cases h0 : s = 0
      · subst h0; rw [monomial_zero']; exact hDC r
      · obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
        have hk' : s k ≠ 0 := by simpa using hk
        have hs' : Finsupp.single k 1 + (s - Finsupp.single k 1) = s := by
          ext x
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hx
          · subst hx; omega
          · simp
        have hXm : monomial s r = (X k : PX m n) * monomial (s - Finsupp.single k 1) r := by
          rw [X, monomial_mul, one_mul, hs']
        rw [hXm, hDX, pderiv_monomial]
        have hlt : ∑ x, ((s - Finsupp.single k 1 - Finsupp.single (flip k) 1 : Fin m × Fin n × Bool →₀ ℕ) x) < N :=
          hs ▸ deg_lt s k hk' _ (fun x => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; exact tsub_le_self)
        rw [ih _ hlt _ rfl, mul_zero]
  intro p
  have hD0 : D p = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s r => exact hmono _ s rfl r
    | add p q hp hq => rw [hDadd, hp, hq, add_zero]
  exact sub_eq_zero.1 hD0

theorem fockMom_of_basic (hB : FockBasic) : FockMom := fockMom_of hB oneMom

end PositivityTheory.Rg.Sw.LC
