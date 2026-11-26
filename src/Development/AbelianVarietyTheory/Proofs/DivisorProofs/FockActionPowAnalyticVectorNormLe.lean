module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderiv
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockNormBound

theorem norm_sum_sq_of_orth {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset κ) (v : κ → H) (h : ∀ a b, a ≠ b → inner ℂ (v a) (v b) = 0) :
    ‖∑ a ∈ s, v a‖ ^ 2 = ∑ a ∈ s, ‖v a‖ ^ 2 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]
  · intro b _ hb; exact h a b (Ne.symm hb)
  · intro h'; exact absurd ha h'

def mfact {σ : Type} (α : σ →₀ ℕ) : ℝ := α.prod (fun _ k => (k.factorial : ℝ))

theorem mfact_nonneg {σ : Type} (α : σ →₀ ℕ) : 0 ≤ mfact α :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem mfact_add {σ : Type} [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  unfold mfact
  rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp),
    ← Finsupp.mul_prod_erase' α i _ (by simp)]
  have : Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α := by
    ext j; by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
  rw [this]
  simp [Nat.factorial_succ]
  ring

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem norm_mono (h : IsFockIP ι) (α : σ →₀ ℕ) : ‖ι (monomial α 1)‖ ^ 2 = mfact α := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]
  have : α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ) := by
    simp [mfact, Finsupp.prod]
  rw [this]; simp

theorem norm_comb (h : IsFockIP ι) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ)
    (g : (σ →₀ ℕ) → (σ →₀ ℕ)) (hg : ∀ a b, a ≠ b → c a ≠ 0 → c b ≠ 0 → g a ≠ g b) :
    ‖ι (∑ a ∈ s, monomial (g a) (c a))‖ ^ 2 = ∑ a ∈ s, ‖c a‖ ^ 2 * mfact (g a) := by
  have e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1) := by
    intro a; rw [← map_smul, smul_monomial]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, norm_sum_sq_of_orth]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [e, norm_smul, mul_pow, norm_mono h]
  · intro a b hab
    rw [e, e]
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    rw [inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]; simp

theorem fock_norm_bounds (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (h : IsFockIP ι) (i : σ) (d : ℕ)
    (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧
      ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  have hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d := by
    intro a ha
    have h1 : a i ≤ P.degreeOf i := monomial_le_degreeOf i ha
    exact_mod_cast h1.trans ((degreeOf_le_totalDegree P i).trans hP)
  have h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := by
    conv_lhs => rw [P.as_sum]
    exact norm_comb h _ _ id (fun a b hab _ _ => hab)
  have h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (AddMonoidAlgebra.coeff P a) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X, monomial_mul, add_comm, one_mul]
  have h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (AddMonoidAlgebra.coeff P a * a i) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_monomial]
  have hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    intro a ha
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))
  constructor
  · rw [h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [mfact_add]
    have := hd a ha
    have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
    nlinarith
  · rw [h2, norm_comb h, h0, Finset.mul_sum]
    · refine Finset.sum_le_sum fun a ha => ?_
      have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
      by_cases hz : a i = 0
      · simp only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (by positivity) h3
      have h4 := mfact_add (a - Finsupp.single i 1) i
      rw [hsub a hz] at h4
      have h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i := by
        have := congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        exact_mod_cast this
      rw [h5] at h4
      rw [norm_mul, Complex.norm_natCast]
      calc (‖AddMonoidAlgebra.coeff P a‖ * a i) ^ 2 * mfact (a - Finsupp.single i 1)
          = a i * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := by rw [h4]; ring
        _ ≤ d * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := mul_le_mul_of_nonneg_right (hd a ha) h3
    · intro a b hab ha hb hh
      have ha' : a i ≠ 0 := fun z => ha (by simp [z])
      have hb' : b i ≠ 0 := fun z => hb (by simp [z])
      apply hab
      rw [← hsub a ha', hh, hsub b hb']

end GlobalTheory.FockNormBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderivStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_norm_bounds_mul_X_pderiv : ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι → ∀ (i : σ) (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d → ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧ ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  first | exact @GlobalTheory.FockNormBound.fock_norm_bounds | exact GlobalTheory.FockNormBound.fock_norm_bounds | (intros; apply GlobalTheory.FockNormBound.fock_norm_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLe
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAnalytic

theorem totalDegree_pderiv_le_self {σ : Type} (i : σ) (Q : MvPolynomial σ ℂ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff Q (m + Finsupp.single i 1) ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree
  omega

def OneStep {σ : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (A : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d →
    (A P).totalDegree ≤ d + 1 ∧ ‖ι (A P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2

section
variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem oneStep_mul (h : IsFockIP ι) (i : σ) : OneStep ι (LinearMap.mulLeft ℂ (X i)) := by
  intro d P hP
  refine ⟨?_, (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).1⟩
  rw [LinearMap.mulLeft_apply]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]; omega

theorem oneStep_pderiv (h : IsFockIP ι) (i : σ) : OneStep ι (pderiv i).toLinearMap := by
  intro d P hP
  refine ⟨((totalDegree_pderiv_le_self i P).trans hP).trans (Nat.le_succ _), ?_⟩
  have := (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).2
  have h2 := sq_nonneg ‖ι P‖
  change ‖ι (pderiv i P)‖ ^ 2 ≤ _
  nlinarith

omit [DecidableEq σ] in
theorem OneStep.neg {A : Module.End ℂ (MvPolynomial σ ℂ)} (h : OneStep ι A) : OneStep ι (-A) := by
  intro d P hP
  simpa using h d P hP

omit [DecidableEq σ] in
theorem OneStep.comp {A B : Module.End ℂ (MvPolynomial σ ℂ)} (hA : OneStep ι A) (hB : OneStep ι B)
    (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ((A * B) P).totalDegree ≤ d + 2 ∧ ‖ι ((A * B) P)‖ ≤ ((d : ℝ) + 3 / 2) * ‖ι P‖ := by
  obtain ⟨h1, h2⟩ := hB d P hP
  obtain ⟨h3, h4⟩ := hA (d + 1) _ h1
  refine ⟨h3, ?_⟩
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  push_cast at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (d : ℝ) + 1 + 1 by positivity)
  have h6 := sq_nonneg ‖ι P‖
  change ‖ι (A (B P))‖ ^ 2 ≤ _
  nlinarith
end

section
variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Pol p q r s →ₗ[ℂ] H}

theorem omE_bound (h : IsFockIP ι) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s)
    (hP : P.totalDegree ≤ d) :
    (omE l l' P).totalDegree ≤ d + 2 ∧ ‖ι (omE l l' P)‖ ≤ ((d : ℝ) + 2) * ‖ι P‖ := by
  have hA : OneStep ι (raiB l) := by
    unfold raiB; split_ifs
    exacts [oneStep_mul h l, (oneStep_pderiv h l).neg]
  have hB : OneStep ι (lowB l') := by
    unfold lowB; split_ifs
    exacts [oneStep_pderiv h l', oneStep_mul h l']
  obtain ⟨h1, h2⟩ := hA.comp hB d P hP
  have hn := norm_nonneg (ι P)
  unfold omE
  split_ifs
  · rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨(totalDegree_add _ _).trans (max_le h1 ((totalDegree_smul_le _ _).trans (by omega))), ?_⟩
    rw [map_add (f := _), map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  · rw [add_zero]
    exact ⟨h1, by linarith⟩

theorem omAct_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ)
    (P : Pol p q r s) (hP : P.totalDegree ≤ d) :
    (omAct p q r s Y P).totalDegree ≤ d + 2 ∧
      ‖ι (omAct p q r s Y P)‖ ≤ (∑ l, ∑ l', ‖Y l l'‖) * (((d : ℝ) + 2) * ‖ι P‖) := by
  have e : omAct p q r s Y P = ∑ l, ∑ l', Y l l' • omE l l' P := by
    simp [omAct, LinearMap.sum_apply]
  rw [e]
  constructor
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
    exact (totalDegree_smul_le _ _).trans (omE_bound h l l' d P hP).1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l' _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (omE_bound h l l' d P hP).2 (norm_nonneg _)

theorem omAct_pow_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d m : ℕ)
    (hm : d ≤ 2 * m) (P : Pol p q r s) (hP : P.totalDegree ≤ d) (k : ℕ) :
    ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧
      ‖ι ((omAct p q r s Y ^ k) P)‖ ≤
        (2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖ := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := omAct_bound h Y _ _ ih.1
    refine ⟨by omega, h2.trans ?_⟩
    have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
    have hm' : (d : ℝ) ≤ 2 * m := by exact_mod_cast hm
    rw [Nat.ascFactorial_succ]
    push_cast
    calc _ ≤ (∑ l, ∑ l', ‖Y l l'‖) * ((2 * ((m : ℝ) + 1 + k)) *
            ((2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS
          exact mul_le_mul (by linarith) ih.2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
end

theorem omAct_pow_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  intro p q r s H _ _ ι h Y d k P hP
  obtain ⟨h1, h2⟩ := omAct_pow_bound h Y d ((d + 1) / 2) (by omega) P hP k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  set m := (d + 1) / 2 with hm
  have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
  generalize (∑ l, ∑ l', ‖Y l l'‖) = S at hS
  have hm1 : (m : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have : 2 * m ≤ d + 2 := by omega
    have : (2 * m : ℝ) ≤ d + 2 := by exact_mod_cast this
    linarith
  have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ ((d : ℝ) / 2 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  have h4 : (((m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (m + k) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  calc (2 * S) ^ k * ((k.factorial : ℝ) * ((m + k).choose k : ℝ))
      ≤ (2 * S) ^ k * ((k.factorial : ℝ) * 2 ^ (m + k)) := by gcongr
    _ = (4 * S) ^ k * (k.factorial : ℝ) * 2 ^ m := by
        rw [show (4 : ℝ) * S = 2 * (2 * S) by ring, mul_pow 2 (2 * S), pow_add]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.FockAnalytic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAction_pow_analyticVector_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  first | exact @GlobalTheory.FockAnalytic.omAct_pow_norm_le | exact GlobalTheory.FockAnalytic.omAct_pow_norm_le | (intros; apply GlobalTheory.FockAnalytic.omAct_pow_norm_le <;> assumption)
end
