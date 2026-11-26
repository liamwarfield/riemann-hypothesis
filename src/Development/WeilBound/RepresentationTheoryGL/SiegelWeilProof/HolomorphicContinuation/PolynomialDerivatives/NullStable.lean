module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SumPderivXMem
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivQuadraticPairing
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullOperatorEvaluation
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  unfold mom
  rw [← integral_add (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp [evX, add_mul]

theorem mom_C_mul (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by
  unfold mom
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [evX, mul_assoc]

theorem mom_sub (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P - Q) = mom c P - mom c Q := by
  unfold mom
  rw [← integral_sub (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp [evX, sub_mul]

theorem mom_sum (c : ℝ) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    mom c (∑ i ∈ s, f i) = ∑ i ∈ s, mom c (f i) := by
  unfold mom
  rw [← MeasureTheory.integral_finsetSum s (fun i _ => integrable_pg c hc (f i))]
  congr 1
  funext x
  simp [evX, Finset.sum_mul]

theorem pderiv_Sg (c : ℝ) (k : Fin m × Fin n × Bool) :
    pderiv k (Sg c : PX m n) = C (-(c : ℂ)) * X (k.1, k.2.1, !k.2.2) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [Sg, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_comm, ite_and,
    Finset.sum_ite_eq', Finset.sum_ite_eq]

def Qv (c : ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) : PX m n :=
  ∑ k, C (crd k v) * (pderiv k P + P * pderiv k (Sg c))

theorem hasFDerivAt_pg (c : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => evX P y * gs c y) (evX P x • (gs c x • dP (Sg c) x) + gs c x • dP P x) x := by
  have hg : HasFDerivAt (fun y : Fin m → Fin n → ℂ => gs c y) (gs c x • dP (Sg c) x) x := by
    have h := (hasFDerivAt_evX (Sg c) x).cexp
    have he : (fun y : Fin m → Fin n → ℂ => gs c y) = fun y => Complex.exp (evX (Sg c) y) :=
      funext (gs_eq c)
    rw [he, gs_eq]
    exact h
  exact (hasFDerivAt_evX P x).mul hg

theorem fderiv_pg (c : ℝ) (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    fderiv ℝ (fun y => evX P y * gs c y) x v = evX (Qv c P v) x * gs c x := by
  rw [(hasFDerivAt_pg c P x).fderiv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP,
    ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem integral_fderiv_pg (c : ℝ) (hc : 0 < c) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    mom c (Qv c P v) = 0 := by
  unfold mom
  have e : (fun x => evX (Qv c P v) x * gs c x) =
      fun x => (1 : ℂ) * fderiv ℝ (fun y => evX P y * gs c y) x v := by
    funext x
    rw [fderiv_pg, one_mul]
  rw [e, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  · simp
  · simp
  · simpa [fderiv_pg] using integrable_pg c hc (Qv c P v)
  · simpa using integrable_pg c hc P
  · intro x _
    exact differentiableAt_const _
  · intro x _
    exact (hasFDerivAt_pg c P x).differentiableAt

def ev1 (k : Fin m × Fin n × Bool) (z : ℂ) : Fin m → Fin n → ℂ := fun a i => if a = k.1 ∧ i = k.2.1 then z else 0

theorem null_operator_evaluation (c : ℝ) (P : PX m n) (k : Fin m × Fin n × Bool) (z : ℂ) :
    Qv c P (ev1 k z) = C z * (pderiv (k.1, k.2.1, false) P + P * pderiv (k.1, k.2.1, false) (Sg c)) +
      C (star z) * (pderiv (k.1, k.2.1, true) P + P * pderiv (k.1, k.2.1, true) (Sg c)) := by
  obtain ⟨a, i, b⟩ := k
  unfold Qv
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Fintype.sum_prod_type, Finset.sum_eq_single i,
    Fintype.sum_bool]
  · simp [crd_apply, ev1, add_comm]
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp

theorem mom_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (P : PX m n) :
    mom c (pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P) = 0 := by
  obtain ⟨a, i, b⟩ := k
  have h1 := integral_fderiv_pg c hc P (ev1 (a, i, b) 1)
  have h2 := integral_fderiv_pg c hc P (ev1 (a, i, b) Complex.I)
  rw [null_operator_evaluation, mom_add c hc, mom_C_mul, mom_C_mul] at h1 h2
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 h2
  have hu : mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
    have h3 : 2 * Complex.I * mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
      linear_combination h2 + Complex.I * h1
    simpa [Complex.I_ne_zero] using h3
  have hw : mom c (pderiv (a, i, true) P + P * pderiv (a, i, true) (Sg c)) = 0 := by
    linear_combination h1 - hu
  have key : pderiv (a, i, b) P - C (c : ℂ) * X (a, i, !b) * P =
      pderiv (a, i, b) P + P * pderiv (a, i, b) (Sg c) := by
    rw [pderiv_Sg, map_neg]
    ring
  rw [key]
  cases b
  · exact hu
  · exact hw

end PositivityTheory.Rg.Sw.LC.NullS
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev QA (ε : Fin m → Bool) : Subalgebra ℂ (PX m n) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))

theorem sgn_mul_self (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem Qp_eq (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * (X (a, i, true) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgn; cases ε a <;> simp

theorem Qp_mem (ε : Fin m → Bool) (i j : Fin n) : (Qp ε i j : PX m n) ∈ QA ε :=
  Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem pd_Qp_f (ε : Fin m → Bool) (a : Fin m) (i k l : Fin n) :
    pderiv (a, i, false) (Qp ε k l : PX m n) = if l = i then C (sgn ε a) * X (a, k, true) else 0 := by
  rw [Qp_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : l = i <;> simp [h]

theorem partial_deriv_quadratic_pairing (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by
  rw [Qp_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : k = j <;> simp [h]

end PositivityTheory.Rg.Sw.LC.NullS
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem fun_mem (ε : Fin m → Bool) (f : PX m n → PX m n) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) = x * f y + y * f x) (hC : ∀ r : ℂ, f (algebraMap ℂ (PX m n) r) = 0)
    (hgen : ∀ i j, f (Qp ε i j) ∈ QA ε) : ∀ R ∈ QA ε, f R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨i, j⟩, rfl⟩ := hx; exact hgen i j
  | algebraMap r => rw [hC]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd]; exact add_mem hx hy
  | mul x y hx' hy' hx hy => rw [hmul]; exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)

def dPhi (c : ℝ) (k : Fin m × Fin n × Bool) (P : PX m n) : PX m n := pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P

theorem mom_mul_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (U P : PX m n) :
    mom c (U * dPhi c k P) = -mom c (pderiv k U * P) := by
  have h := mom_dPhi c hc k (U * P)
  have e : U * dPhi c k P =
      (pderiv k (U * P) - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * (U * P)) - pderiv k U * P := by
    unfold dPhi
    rw [(pderiv k).leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, mom_sub c hc, h, zero_sub]

theorem pderiv_X_mem (ε : Fin m → Bool) (k l : Fin m × Fin n × Bool) : (pderiv k (X l : PX m n)) ∈ QA ε := by
  rw [pderiv_X, Pi.single_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

def fE (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, j, false) * pderiv (a, i, false) R

def fA (i j : Fin n) (R : PX m n) : PX m n := ∑ a, X (a, i, true) * pderiv (a, j, true) R

private theorem sum_X_mul_pderiv_mem_QA_of_generators (ε : Fin m → Bool) (g h : Fin m → Fin m × Fin n × Bool)
    (hgen : ∀ k l, (∑ a, X (g a) * pderiv (h a) (Qp ε k l) : PX m n) ∈ QA ε) :
    ∀ R ∈ QA ε, (∑ a, X (g a) * pderiv (h a) R : PX m n) ∈ QA ε := by
  apply fun_mem ε (fun R => ∑ a, X (g a) * pderiv (h a) R)
  · intro x y
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
  · intro x y
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun a _ => by ring)
  · intro r
    simp [Derivation.map_algebraMap]
  · exact hgen

theorem fE_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fE i j R ∈ QA ε := by
  intro R hR
  unfold fE
  refine sum_X_mul_pderiv_mem_QA_of_generators ε (fun a => (a, j, false)) (fun a => (a, i, false)) (fun k l => ?_) R hR
  simp only [pd_Qp_f]
  by_cases h : l = i
  · subst h
    have e : (∑ a, X (a, j, false) * (C (sgn ε a) * X (a, k, true)) : PX m n) = Qp ε k j := by
      rw [Qp_eq]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    simp only [if_true]
    rw [e]
    exact Qp_mem ε k j
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    exact zero_mem _

theorem fA_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fA i j R ∈ QA ε := by
  intro R hR
  unfold fA
  refine sum_X_mul_pderiv_mem_QA_of_generators ε (fun a => (a, i, true)) (fun a => (a, j, true)) (fun k l => ?_) R hR
  simp only [partial_deriv_quadratic_pairing]
  by_cases h : k = j
  · subst h
    have e : (∑ a, X (a, i, true) * (C (sgn ε a) * X (a, l, false)) : PX m n) = Qp ε i l := by
      rw [Qp_eq]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    simp only [if_true]
    rw [e]
    exact Qp_mem ε i l
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
    exact zero_mem _

def Bf (ε : Fin m → Bool) (i j : Fin n) (U V : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, j, true) U * pderiv (a, i, false) V + pderiv (a, i, false) U * pderiv (a, j, true) V)

theorem Bf_comm (ε : Fin m → Bool) (i j : Fin n) (U V : PX m n) : Bf ε i j U V = Bf ε i j V U := by
  unfold Bf; exact Finset.sum_congr rfl fun _ _ => by ring

theorem Bf_der (ε : Fin m → Bool) (i j : Fin n) (U : PX m n) (hU : ∀ k l, Bf ε i j U (Qp ε k l) ∈ QA ε) :
    ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε :=
  fun_mem ε _ (fun x y => by simp only [Bf, map_add (f := _), mul_add, ← Finset.sum_add_distrib];
                             exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y => by simp only [Bf, Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib];
                   exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun r => by simp [Bf]) hU

theorem sgn3 (ε : Fin m → Bool) (a : Fin m) :
    (C (sgn ε a) : PX m n) * (C (sgn ε a) * C (sgn ε a)) = C (sgn ε a) := by
  rw [← map_mul, sgn_mul_self, map_one, mul_one]

theorem sumT (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, l, false) else 0) *
      (if q then C (sgn ε a) * X (a, k, true) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, and_self, and_true, and_false,
    true_and, false_and, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [Qp_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  linear_combination (X (a, k, true) * X (a, l, false) : PX m n) * sgn3 ε a

theorem sumT' (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, k, true) else 0) *
      (if q then C (sgn ε a) * X (a, l, false) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, and_self, and_true, and_false,
    true_and, false_and, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [Qp_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  linear_combination (X (a, k, true) * X (a, l, false) : PX m n) * sgn3 ε a

theorem ite_mem (ε : Fin m → Bool) (p : Prop) [Decidable p] (k l : Fin n) :
    (if p then (Qp ε k l : PX m n) else 0) ∈ QA ε := by
  split_ifs
  · exact Qp_mem ε k l
  · exact zero_mem _

theorem Bf_gen (ε : Fin m → Bool) (i j k l k' l' : Fin n) :
    Bf ε i j (Qp ε k l) (Qp ε k' l') ∈ QA ε := by
  simp only [Bf, pd_Qp_f, partial_deriv_quadratic_pairing, mul_add, Finset.sum_add_distrib, sumT, sumT']
  exact add_mem (ite_mem _ _ _ _) (ite_mem _ _ _ _)

theorem Bf_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ U ∈ QA ε, ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε := by
  intro U hU
  apply Bf_der ε i j U
  intro k l
  rw [Bf_comm]
  exact Bf_der ε i j (Qp ε k l) (fun k' l' => Bf_gen ε i j k l k' l') U hU

def fL (ε : Fin m → Bool) (i j : Fin n) (R : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * pderiv (a, j, true) (pderiv (a, i, false) R)

theorem fL_mem (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fL ε i j R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, l⟩, rfl⟩ := hx
    have : fL ε i j (Qp ε k l : PX m n) =
        ∑ a, C (sgn ε a) * pderiv (a, j, true) (if l = i then C (sgn ε a) * X (a, k, true) else 0) := by
      simp only [fL, pd_Qp_f]
    rw [this]
    refine sum_mem fun a _ => mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) ?_
    split_ifs
    · rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
      exact mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) (pderiv_X_mem ε _ _)
    · simp
  | algebraMap r => simp [fL]
  | add x y _ _ hx hy => simpa [fL, mul_add, Finset.sum_add_distrib] using add_mem hx hy
  | mul x y hx' hy' hx hy =>
    have e : fL ε i j (x * y) = x * fL ε i j y + y * fL ε i j x + Bf ε i j x y := by
      simp only [fL, Bf, Derivation.leibniz, smul_eq_mul, map_add (f := _), Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact add_mem (add_mem (mul_mem hx' hy) (mul_mem hy' hx)) (Bf_mem ε i j x hx' y hy')

theorem sum_pderiv_X_mem (ε : Fin m → Bool) (R : PX m n) (hR : R ∈ QA ε) (f : Fin m → Fin m × Fin n × Bool)
    (g : Fin m → Fin m × Fin n × Bool) : (∑ a, R * pderiv (f a) (X (g a) : PX m n)) ∈ QA ε := by
  apply Subalgebra.sum_mem
  intro a _
  exact mul_mem hR (pderiv_X_mem ε _ _)

theorem nullStable : NullStable := by
  intro m n ε c hc i j P hP
  have hP' : ∀ R ∈ QA ε, mom c (R * P) = 0 := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    have e : R * lapS ε c i j P =
        ∑ a, (C (sgn ε a) * R) * dPhi c (a, i, false) (dPhi c (a, j, true) P) := by
      simp only [lapS, dPhi, Finset.mul_sum, Bool.not_false, Bool.not_true]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, pderiv_C_mul, neg_neg]
    rw [← mom_sum c hc]
    have e3 : (∑ a, C (sgn ε a) * pderiv (a, j, true) (pderiv (a, i, false) R) * P) =
        fL ε i j R * P := by
      simp only [fL, Finset.sum_mul]
    rw [e3]
    exact hP' _ (fL_mem ε i j R hR)
  · intro R hR
    have e : R * eulH c i j P = ∑ a, (R * X (a, j, false)) * dPhi c (a, i, false) P := by
      simp only [eulH, dPhi, Finset.mul_sum, Bool.not_false]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, Derivation.leibniz, smul_eq_mul]
    rw [Finset.sum_neg_distrib, ← mom_sum c hc]
    have e3 : (∑ a, (R * pderiv (a, i, false) (X (a, j, false)) + X (a, j, false) * pderiv (a, i, false) R) * P) =
        ((∑ a, R * pderiv (a, i, false) (X (a, j, false) : PX m n)) + fE i j R) * P := by
      simp only [fE, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hS : ((∑ a, R * pderiv (a, i, false) (X (a, j, false) : PX m n)) + fE i j R) ∈ QA ε :=
      add_mem (sum_pderiv_X_mem ε R hR (fun a => (a, i, false)) (fun a => (a, j, false)))
        (fE_mem ε i j R hR)
    rw [e3, hP' _ hS, neg_zero]
  · intro R hR
    have e : R * eulA c i j P = ∑ a, (R * X (a, i, true)) * dPhi c (a, j, true) P := by
      simp only [eulA, dPhi, Finset.mul_sum, Bool.not_true]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, mom_sum c hc]
    simp only [mom_mul_dPhi c hc, Derivation.leibniz, smul_eq_mul]
    rw [Finset.sum_neg_distrib, ← mom_sum c hc]
    have e3 : (∑ a, (R * pderiv (a, j, true) (X (a, i, true)) + X (a, i, true) * pderiv (a, j, true) R) * P) =
        ((∑ a, R * pderiv (a, j, true) (X (a, i, true) : PX m n)) + fA i j R) * P := by
      simp only [fA, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hS : ((∑ a, R * pderiv (a, j, true) (X (a, i, true) : PX m n)) + fA i j R) ∈ QA ε :=
      add_mem (sum_pderiv_X_mem ε R hR (fun a => (a, j, true)) (fun a => (a, i, true)))
        (fA_mem ε i j R hR)
    rw [e3, hP' _ hS, neg_zero]
  · intro R hR
    simp only [mulQ, ← mul_assoc]
    exact hP' _ (mul_mem hR (Qp_mem ε i j))

end PositivityTheory.Rg.Sw.LC.NullS
end
end

namespace PositivityTheory.Rg.Sw.LC

theorem nullStable : NullStable := NullS.nullStable

end PositivityTheory.Rg.Sw.LC
