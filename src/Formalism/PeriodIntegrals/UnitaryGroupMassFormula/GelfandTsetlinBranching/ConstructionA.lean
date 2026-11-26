module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FixedLineProofA
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ProdMkPtA
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.CoeffRowActDiagA
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

theorem emb_cc_A (g : GL (Fin n) ℂ) (i j : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_cl_A (g : GL (Fin n) ℂ) (i : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_lc_A (g : GL (Fin n) ℂ) (i : Fin n) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.last n) (Fin.castSucc i) = 0 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem emb_ll_A (g : GL (Fin n) ℂ) :
    ((embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Fin.last n) (Fin.last n) = 1 := by
  simp [embGL, blkHom, Matrix.reindexAlgEquiv_apply]

theorem det_emb_unitri_A (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := by
  first | exact UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A .. | (apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl hd | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n

theorem eval_rowAct_A {r c : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x : Fin r × Fin c → ℂ)
    (f : MvPolynomial (Fin r × Fin c) ℂ) :
    eval x (rowAct ℂ M f) = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) f := by
  have h : (eval x).comp (rowAct ℂ (n := c) M).toRingHom = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) h

def elemGL_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) : GL (Fin n) ℂ where
  val := 1 + Matrix.single a b t
  inv := 1 - Matrix.single a b t
  val_inv := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [add_mul, one_mul, mul_sub, mul_one, h]
    abel
  inv_val := by
    have h : Matrix.single a b t * Matrix.single a b t = 0 := by simp [Ne.symm hab]
    rw [sub_mul, one_mul, mul_add, mul_one, h]
    abel

theorem elemGL_apply_A (a b : Fin n) (hab : a ≠ b) (t : ℂ) (i j : Fin n) :
    ((elemGL_A a b hab t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
      (if i = j then 1 else 0) + (if a = i ∧ b = j then t else 0) := by
  show (1 + Matrix.single a b t) i j = _
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem fixed_rowOp_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (a b : Fin n) (hab : a < b) (t : ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) :
    eval (lhwline_rowOp (Fin.castSucc a) (Fin.castSucc b) t x) f = eval x f := by
  have hl : ∀ i j, j < i → ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
    intro i j hji
    rw [elemGL_apply_A, if_neg (ne_of_gt hji), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hji
  have hd : ∀ i, ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
    intro i
    rw [elemGL_apply_A, if_pos rfl, if_neg]
    · simp
    · rintro ⟨rfl, h⟩
      exact hab.ne h.symm
  have hg := hf.1 (elemGL_A a b hab.ne t) hl hd
  unfold sqAct detPow at hg
  rw [det_emb_unitri_A _ hl hd, one_zpow, Units.val_one, one_smul] at hg
  have h2 := congrArg (eval x) hg
  rw [eval_rowAct_A] at h2
  rw [← h2]
  congr 2
  funext v
  obtain ⟨ρ, s⟩ := v
  simp only [Matrix.transpose_apply, Fin.sum_univ_castSucc, lhwline_rowOp]
  induction ρ using Fin.lastCases with
  | last =>
    simp only [emb_cl_A, emb_ll_A, zero_mul, Finset.sum_const_zero, one_mul, zero_add]
    rw [if_neg (Fin.castSucc_lt_last b).ne']
  | cast ρ =>
    simp only [emb_cc_A, emb_lc_A, zero_mul, add_zero, elemGL_apply_A, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ ρ, if_pos (Finset.mem_univ _)]
    by_cases hρ : ρ = b
    · subst hρ
      rw [if_pos rfl]
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc
        rw [if_neg (fun h => hc h.1.symm)]
      · simp
    · rw [if_neg (fun h => hρ (Fin.castSucc_injective _ h))]
      rw [Finset.sum_eq_zero]
      · simp
      · intro c _
        rw [if_neg (fun h => hρ h.2.symm)]

theorem weight_row_A {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (ρ : Fin r) :
    Finsupp.weight (rowW r c) m ρ = ∑ s : Fin c, m (ρ, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ρ]
  · simp [rowW]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

theorem coeff_rowAct_diag_A {r c : ℕ} (s : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin c) ℂ)
    (m : Fin r × Fin c →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowAct ℂ (Matrix.diagonal s) f) m = (∏ ρ, s ρ ^ (∑ j : Fin c, m (ρ, j))) * AddMonoidAlgebra.coeff f m := by
  induction f using MvPolynomial.induction_on' with
  | monomial m' k =>
    rw [rowActDiagWeight ℂ r c s _ _ (isWeightedHomogeneous_monomial _ _ _ rfl), coeff_smul, coeff_monomial,
      smul_eq_mul]
    split_ifs with h
    · subst h
      simp only [weight_row_A]
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem zpow_two_inj_A (a b : ℤ) (h : (2 : ℂ) ^ a = 2 ^ b) : a = b := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow] at h2
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h3] at h2
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h2

theorem fixed_rowDeg_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : m ∈ f.support) (a : Fin n) :
    ((∑ s, m (Fin.castSucc a, s) : ℕ) : ℤ) + lam.detShift = mu.w a := by
  set t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 2 two_ne_zero else 1 with ht
  have hg := hf.2 t
  have hdiag : ((embGL ℂ n (n + 1) rfl (diagGL ℂ n t) : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Matrix.diagonal (fun c => if c = Fin.castSucc a then (2 : ℂ) else 1) := by
    ext ρ c
    rw [Matrix.transpose_apply, Matrix.diagonal_apply]
    induction ρ using Fin.lastCases with
    | last =>
      induction c using Fin.lastCases with
      | last => simp [emb_ll_A, (Fin.castSucc_lt_last a).ne']
      | cast c => simp [emb_cl_A, (Fin.castSucc_lt_last c).ne']
    | cast ρ =>
      induction c using Fin.lastCases with
      | last => simp [emb_lc_A, (Fin.castSucc_lt_last ρ).ne]
      | cast c =>
        rw [emb_cc_A]
        simp only [diagGL, Matrix.diagonal_apply, ht, Fin.castSucc_inj]
        by_cases hc : c = ρ
        · subst hc
          by_cases hca : c = a <;> simp [hca]
        · simp [hc, Ne.symm hc]
  have hdet : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) : ℂˣ) : ℂ) = 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hdiag, Matrix.det_diagonal,
      Fintype.prod_ite_eq']
  unfold sqAct detPow at hg
  rw [hdiag] at hg
  have hc := congrArg (AddMonoidAlgebra.coeff · m) hg
  rw [coeff_smul, coeff_smul, coeff_rowAct_diag_A, smul_eq_mul, smul_eq_mul, Units.val_zpow_eq_zpow_val, hdet]
    at hc
  have hcf : AddMonoidAlgebra.coeff f m ≠ 0 := mem_support_iff.mp hm
  have hprod : (∏ ρ : Fin (n + 1), (if ρ = Fin.castSucc a then (2 : ℂ) else 1) ^ (∑ j, m (ρ, j))) =
      2 ^ (∑ j, m (Fin.castSucc a, j)) := by
    rw [Finset.prod_eq_single (Fin.castSucc a)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hmu : ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) = 2 ^ mu.w a := by
    rw [Units.coe_prod, Finset.prod_eq_single a]
    · simp [ht]
    · intro b _ hb
      simp [ht, hb]
    · simp
  rw [hprod, hmu, ← mul_assoc] at hc
  have hc2 := mul_right_cancel₀ hcf hc
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero] at hc2
  have := zpow_two_inj_A _ _ hc2
  omega

end PI.WGB
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.StepACleared
noncomputable section

namespace PI.WGB

open Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def RInvA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) : Prop :=
  ∀ (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a b : Fin (n + 1)) (t : ℂ), a < b → b.val < n →
    φ (lhwline_rowOp a b t x) = φ x

theorem mrow_invA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hφ : RInvA φ) (p : Fin (n + 1))
    (t : Fin (n + 1) → ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (S : Finset (Fin (n + 1)))
    (hS : ∀ b ∈ S, p < b ∧ b.val < n) :
    φ (lhwline_mrow p S t x) = φ x := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
  | insert b S hb ih =>
    have hpS : p ∉ S := fun h => lt_irrefl p (hS p (Finset.mem_insert_of_mem h)).1
    have hpb := hS b (Finset.mem_insert_self b S)
    have heq : lhwline_mrow p (insert b S) t x = lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      simp only [lhwline_mrow, lhwline_rowOp, Finset.mem_insert]
      by_cases hv : v.1 = b
      · simp [hv, hb, hpS]
      · simp [hv]
    rw [heq, hφ _ p b _ hpb.1 hpb.2, ih fun b' hb' => hS b' (Finset.mem_insert_of_mem hb')]

def stepA (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b ∧ b.val < n) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y

theorem stepA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (stepA p q x) = φ x := by
  unfold stepA
  simp only
  rw [lhwline_mcol_inv φ hC _ _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2),
    mrow_invA φ hR _ _ _ _ (fun b hb => (Finset.mem_filter.mp hb).2)]

def elimA : ℕ → (Fin (n + 1) × Fin (n + 1) → ℂ) → (Fin (n + 1) × Fin (n + 1) → ℂ)
  | 0, x => x
  | k + 1, x =>
    if h : k < n then stepA ⟨k, by omega⟩ ⟨k, by omega⟩ (elimA k x) else elimA k x

theorem elimA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (elimA k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [elimA]
    split_ifs
    · rw [stepA_inv φ hR hC, ih]
    · exact ih

def clearedA (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ (a j : Fin (n + 1)), a.val < n → a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0

theorem stepA_apply (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a j : Fin (n + 1)) :
    stepA p q x (a, j) =
      (if p < a ∧ a.val < n then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a ∧ a.val < n then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [stepA, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ, true_and,
    lt_irrefl, false_and, if_false]
  split_ifs <;> ring

theorem stepA_cleared (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hp : y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0) :
    clearedA (k + 1) (stepA ⟨k, by omega⟩ ⟨k, by omega⟩ y) := by
  intro a j ha hne hlt
  rw [stepA_apply]
  simp only [Fin.lt_def]
  rcases lt_trichotomy j.val k with hj | hj | hj
  · have h1 : y (⟨k, by omega⟩, j) = 0 := hy _ _ (by show k < n; omega) (by show k ≠ j.val; omega) (Or.inr hj)
    have h2 : y (a, j) = 0 := hy _ _ ha hne (Or.inr hj)
    rw [if_neg (show ¬ k < j.val by omega)]
    split_ifs <;> simp [h1, h2]
  · have hjq : j = ⟨k, by omega⟩ := Fin.ext hj
    rw [hjq]
    simp only [Fin.val_mk, lt_irrefl, if_false, add_zero]
    split_ifs with ha'
    · rw [neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
    · rw [← hjq]
      exact hy _ _ ha hne (Or.inl (by omega))
  · have ha2 : a.val ≤ k := by omega
    have hka : ¬ (k < a.val ∧ a.val < n) := by omega
    simp only [if_neg hka, if_pos hj]
    rcases lt_or_eq_of_le ha2 with ha2 | ha2
    · have h1 : y (a, j) = 0 := hy _ _ ha hne (Or.inl ha2)
      have h2 : y (a, ⟨k, by omega⟩) = 0 := hy _ _ ha (by show a.val ≠ k; omega) (Or.inl ha2)
      simp [h1, h2]
    · have hap : a = ⟨k, by omega⟩ := Fin.ext ha2
      rw [hap, neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]

theorem pivotA_ne (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hd : eval y (lpMinor ℂ (k + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0 := by
  unfold lpMinor at hd
  rw [RingHom.map_det] at hd
  have hM : (eval y).mapMatrix (Matrix.of fun p q : Fin (k + 1) =>
      (X (Fin.castLE (show k + 1 ≤ n + 1 by omega) p, Fin.castLE (show k + 1 ≤ n + 1 by omega) q) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) =
      Matrix.diagonal (fun p => y (Fin.castLE (show k + 1 ≤ n + 1 by omega) p,
        Fin.castLE (show k + 1 ≤ n + 1 by omega) p)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · have hpq : p.val ≠ q.val := fun e => h (Fin.ext e)
      have := p.isLt
      have := q.isLt
      apply hy
      · simp only [Fin.val_castLE]; omega
      · simpa using hpq
      · simp only [Fin.val_castLE]; omega
  rw [hM, Matrix.det_diagonal] at hd
  have := Finset.prod_ne_zero_iff.mp hd (Fin.last k) (Finset.mem_univ _)
  convert this using 3 <;> ext <;> simp

theorem minorA_RInv (s : ℕ) (hr : s ≤ n + 1) :
    RInvA (fun x : Fin (n + 1) × Fin (n + 1) → ℂ => eval x (lpMinor ℂ s hr hr)) :=
  fun x a b t hab _ => lhwline_minor_RInv s hr hr x a b t hab

theorem elimA_cleared (x : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    ∀ k, k ≤ n → clearedA k (elimA k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ _ h
    omega
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hc := ih (by omega)
    simp only [elimA, dif_pos hkn]
    apply stepA_cleared k hkn _ hc
    apply pivotA_ne k hkn _ hc
    have hk1 : k + 1 ≤ n + 1 := by omega
    rw [elimA_inv (fun y => eval y (lpMinor ℂ (k + 1) hk1 hk1 :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ))
      (minorA_RInv _ _) (lhwline_minor_CInv _ _ _)]
    exact hx k hkn

theorem vanishA (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hR : RInvA (fun x => eval x g)) (hC : lhwline_CInv (fun x => eval x g))
    (hD : ∀ D : Fin (n + 1) × Fin (n + 1) → ℂ,
      (∀ a j : Fin (n + 1), a.val < n → a ≠ j → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  set P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ := ∏ s : Fin n,
    lpMinor ℂ (s.val + 1) (by have := s.isLt; omega) (by have := s.isLt; omega) with hPdef
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (eval (idPoint ℂ (n + 1) (n + 1))) h
    simp only [hPdef, map_prod, eval_idPoint_lpMinor, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hgP : g * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0
    · have h1 : eval x g = eval (elimA n x) g :=
        (elimA_inv (fun y => eval y g) hR hC n x).symm
      rw [h1, hD _ (fun a j ha h => elimA_cleared x hx n le_rfl a j ha
        (fun e => h (Fin.ext e)) (Or.inl ha)), zero_mul]
    · push Not at hx
      obtain ⟨s, hs, hs0⟩ := hx
      have : eval x P = 0 := by
        rw [hPdef, map_prod]
        exact Finset.prod_eq_zero (i := ⟨s, by omega⟩) (Finset.mem_univ _) hs0
      rw [this, mul_zero]
  rcases mul_eq_zero.mp hgP with h | h
  · exact h
  · exact absurd h hP

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def mStarA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) : Fin (n + 1) × Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    Fin.lastCases (Fin.lastCases (ν (Fin.last n)) (fun k => ν (Fin.castSucc k) - kap k) v.2)
      (fun a => Fin.lastCases 0 (fun k => if k = a then kap a else 0) v.2) v.1

@[simp] theorem mStarA_cc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a k : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.castSucc k) = if k = a then kap a else 0 := by
  simp [mStarA]

@[simp] theorem mStarA_cl (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.last n) = 0 := by
  simp [mStarA]

@[simp] theorem mStarA_lc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (k : Fin n) :
    mStarA kap ν (Fin.last n, Fin.castSucc k) = ν (Fin.castSucc k) - kap k := by
  simp [mStarA]

@[simp] theorem mStarA_ll (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) :
    mStarA kap ν (Fin.last n, Fin.last n) = ν (Fin.last n) := by
  simp [mStarA]

def IsDPtA (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ a j : Fin (n + 1), a.val < n → a ≠ j → x (a, j) = 0

theorem mono_eq_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : m ∈ g.support) (hne : ∏ v, x v ^ m v ≠ 0) : m = mStarA kap ν := by
  have hz : ∀ v, x v = 0 → m v = 0 := by
    intro v hv
    by_contra h
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, zero_pow h]))
  have htop : ∀ (a : Fin n) (s : Fin (n + 1)), s ≠ Fin.castSucc a → m (Fin.castSucc a, s) = 0 :=
    fun a s hs => hz _ (hx _ _ (by simp) (Ne.symm hs))
  have hdiag : ∀ a : Fin n, m (Fin.castSucc a, Fin.castSucc a) = kap a := by
    intro a
    rw [← hrow m hm a, Finset.sum_eq_single (Fin.castSucc a)]
    · intro s _ hs
      exact htop a s hs
    · simp
  have hcolsum : ∀ j, ∑ ρ, m (ρ, j) = ν j := by
    intro j
    rw [← lhwline_weight_col, hcol (mem_support_iff.mp hm)]
  ext ⟨ρ, s⟩
  induction ρ using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last =>
      have h := hcolsum (Fin.last n)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun a _ => htop a _ (Fin.castSucc_lt_last a).ne'),
        zero_add] at h
      rw [mStarA_ll, h]
    | cast k =>
      have h := hcolsum (Fin.castSucc k)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_single k] at h
      · rw [hdiag] at h
        rw [mStarA_lc]
        omega
      · intro b _ hb
        exact htop b _ (fun e => hb (Fin.castSucc_injective _ e).symm)
      · simp
  | cast a =>
    induction s using Fin.lastCases with
    | last =>
      rw [mStarA_cl]
      exact htop a _ (Fin.castSucc_lt_last a).ne'
    | cast k =>
      rw [mStarA_cc]
      split_ifs with hka
      · subst hka
        exact hdiag k
      · exact htop a _ (fun e => hka (Fin.castSucc_injective _ e))

theorem eval_D_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) :
    eval x g = AddMonoidAlgebra.coeff g (mStarA kap ν) * ∏ v, x v ^ (mStarA kap ν) v := by
  rw [MvPolynomial.eval_eq']
  by_cases hs : mStarA kap ν ∈ g.support
  · rw [Finset.sum_eq_single (mStarA kap ν)]
    · intro m hm hne
      by_contra hz
      have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
      exact hne (mono_eq_A kap ν g hcol hrow x hx m hm hprod)
    · intro h
      exact absurd hs h
  · have hc : AddMonoidAlgebra.coeff g (mStarA kap ν) = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [hc, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hz
    have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact hs (mono_eq_A kap ν g hcol hrow x hx m hm hprod ▸ hm)

def kapA (lam : DomWeight (n + 1)) (mu : DomWeight n) (a : Fin n) : ℕ := (mu.w a - lam.detShift).toNat

theorem props_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : f ∈ nablaSq ℂ (n + 1) lam) (hfix : IsFixedW rfl lam mu f) :
    IsWeightedHomogeneous (colW (n + 1) (n + 1)) f lam.natW ∧ RInvA (fun x => eval x f) ∧
      lhwline_CInv (fun x => eval x f) ∧
      ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kapA lam mu a := by
  refine ⟨(lsat_mem_dualWeyl.mp hf).1, ?_, ?_, ?_⟩
  · intro x a b t hab hb
    have ha : a.val < n := lt_trans hab hb
    have h1 : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
    have h2 : b = Fin.castSucc ⟨b.val, hb⟩ := Fin.ext rfl
    simp only
    rw [h1, h2]
    exact fixed_rowOp_A lam mu f hfix _ _ (by rw [Fin.lt_def] at hab ⊢; exact hab) t x
  · exact lhwline_CInv_of f (fun l j hlj c => ((dualWeylPoint ℂ (n + 1) (n + 1) lam.natW f).mp hf).2 l j hlj c)
  · intro m hm a
    have := fixed_rowDeg_A lam mu f hfix m hm a
    unfold kapA
    omega

def mkPtA (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun v => Fin.lastCases (z v.2) (fun a => Fin.lastCases 0 (fun k => if k = a then dv a else 0) v.2) v.1

theorem mkPtA_D (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : IsDPtA (mkPtA dv z) := by
  intro a j ha hne
  obtain ⟨a', rfl⟩ : ∃ a' : Fin n, a = Fin.castSucc a' := ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  induction j using Fin.lastCases with
  | last => simp [mkPtA]
  | cast k =>
    simp only [mkPtA, Fin.lastCases_castSucc]
    rw [if_neg]
    rintro rfl
    exact hne rfl

theorem prod_mkPtA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) :
    ∏ v, mkPtA dv z v ^ (mStarA kap ν) v =
      (∏ a, dv a ^ kap a) * (∏ k : Fin n, z (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k)) *
        z (Fin.last n) ^ ν (Fin.last n) := by
  have hpw : ∀ a' k : Fin n, (if k = a' then dv a' else 0) ^ (if k = a' then kap a' else 0) =
      if k = a' then dv a' ^ kap a' else 1 := by
    intro a' k
    split_ifs <;> simp
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_castSucc, mkPtA, hpw, mul_assoc]

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

theorem eval_aeval_poly_A {σ : Type*} (Y : σ → Polynomial ℂ) (f : MvPolynomial σ ℂ) (e : ℂ) :
    (aeval Y f).eval e = eval (fun v => (Y v).eval e) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem eps_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) f ν)
    (hrow : ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (hR : RInvA (fun x => eval x f)) (hC : lhwline_CInv (fun x => eval x f))
    (hc : AddMonoidAlgebra.coeff f (mStarA kap ν) ≠ 0) (i i' : Fin n) (hii : i'.val = i.val + 1)
    (hle : kap i' ≤ ν (Fin.castSucc i')) : ν (Fin.castSucc i') ≤ kap i := by
  by_contra hlt
  push Not at hlt
  have hne : i ≠ i' := by
    intro e
    rw [e] at hii
    omega
  have hlt' : Fin.castSucc i < Fin.castSucc i' := by
    rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def]
    omega
  set νp := ν (Fin.castSucc i') with hνp
  let dv : ℂ → Fin n → ℂ := fun e a => if a = i then e else if a = i' then -1 / e else 1
  let zz : ℂ → Fin (n + 1) → ℂ := fun e s => if s = Fin.castSucc i' then -1 / e else 1
  let Y : Fin (n + 1) × Fin (n + 1) → Polynomial ℂ := fun v =>
    Fin.lastCases (if v.2 = Fin.castSucc i' then 0 else 1)
      (fun a => Fin.lastCases 0 (fun k => if a = i then (if k = i then Polynomial.X else if k = i' then 1 else 0)
        else if a = i' then (if k = i then 1 else 0) else (if k = a then 1 else 0)) v.2) v.1
  have hpt : ∀ e : ℂ, e ≠ 0 → (fun v => (Y v).eval e) =
      lhwline_rowOp (Fin.castSucc i) (Fin.castSucc i') (1 / e)
        (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e))) := by
    intro e he
    funext v
    obtain ⟨ρ, s⟩ := v
    induction ρ using Fin.lastCases with
    | last =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, (Fin.castSucc_lt_last i').ne',
          (Fin.castSucc_lt_last i).ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, zz, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj, (Fin.castSucc_lt_last i').ne', if_false]
        by_cases hk : k = i'
        · subst hk
          simp [hne]
          ring
        · simp [hk]
    | cast a =>
      induction s using Fin.lastCases with
      | last =>
        simp [Y, lhwline_rowOp, lhwline_colOp, mkPtA, (Fin.castSucc_lt_last i').ne']
      | cast k =>
        simp only [Y, lhwline_rowOp, lhwline_colOp, mkPtA, dv, Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.castSucc_inj]
        by_cases ha : a = i
        · subst ha
          have hai : a ≠ i' := hne
          by_cases hk : k = a
          · subst hk
            simp [hai]
          · by_cases hk' : k = i'
            · subst hk'
              simp [hai, hk, Ne.symm hai, hne, Ne.symm hne]
              field_simp
            · simp [hai, hk, hk']
        · by_cases ha' : a = i'
          · subst ha'
            by_cases hk : k = i
            · subst hk
              simp [ha, hne, Ne.symm hne]
              field_simp
            · by_cases hk' : k = a
              · subst hk'
                simp [ha, hk, hne, Ne.symm hne]
                field_simp
                ring
              · simp [ha, hk, hk', Ne.symm hk']
          · by_cases hk : k = i
            · subst hk
              simp [ha, ha', Ne.symm ha, hne, Ne.symm hne]
            · by_cases hk' : k = i'
              · subst hk'
                simp [ha, ha', hk, Ne.symm ha', Ne.symm ha]
              · by_cases hka : k = a <;> simp [ha, ha', hk, hk', hka, Ne.symm ha, Ne.symm ha']
  have hval : ∀ e : ℂ, e ≠ 0 →
      (aeval Y f).eval e = AddMonoidAlgebra.coeff f (mStarA kap ν) * (e ^ kap i * (-1 / e) ^ νp) := by
    intro e he
    have e1 := hR (lhwline_colOp (Fin.castSucc i) (Fin.castSucc i') (1 / e) (mkPtA (dv e) (zz e)))
      (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt' (by simp)
    have e2 := hC (mkPtA (dv e) (zz e)) (Fin.castSucc i) (Fin.castSucc i') (1 / e) hlt'
    simp only at e1 e2
    rw [eval_aeval_poly_A, hpt e he, e1, e2, eval_D_A kap ν f hcol hrow _ (mkPtA_D _ _), prod_mkPtA]
    congr 1
    have h1 : ∏ a, dv e a ^ kap a = e ^ kap i * (-1 / e) ^ kap i' := by
      have : ∀ a, dv e a ^ kap a =
          (if a = i then e ^ kap i else 1) * (if a = i' then (-1 / e) ^ kap i' else 1) := by
        intro a
        by_cases h1 : a = i
        · subst h1
          simp [dv, hne]
        · by_cases h2 : a = i'
          · subst h2
            simp [dv, h1]
          · simp [dv, h1, h2]
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.prod_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have h2 : ∏ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) = (-1 / e) ^ (νp - kap i') := by
      have : ∀ k : Fin n, zz e (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k) =
          if k = i' then (-1 / e) ^ (νp - kap i') else 1 := by
        intro k
        by_cases hk : k = i'
        · subst hk
          simp [zz, hνp]
        · simp [zz, hk]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    have h3 : zz e (Fin.last n) = 1 := by
      simp [zz, (Fin.castSucc_lt_last i').ne']
    rw [h1, h2, h3, one_pow, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  set p := aeval Y f with hp
  set q : Polynomial ℂ := p * Polynomial.X ^ νp -
    Polynomial.C (AddMonoidAlgebra.coeff f (mStarA kap ν) * (-1) ^ νp) * Polynomial.X ^ (kap i) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro e he
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at he
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hq, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hval e he]
    rw [div_pow]
    field_simp
    ring
  have hco := congrArg (fun r : Polynomial ℂ => r.coeff (kap i)) hq0
  simp only [hq, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', Polynomial.coeff_C_mul_X_pow,
    if_neg (not_le.mpr hlt), if_pos rfl, Polynomial.coeff_zero, zero_sub, neg_eq_zero] at hco
  simp at hco
  rcases hco with h | h
  · exact hc h
  · exfalso
    rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.coeff_C_zero] at h
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h

theorem fixedLine_proof_A : FixedLine := by
  intro n N h lam mu f₁ f₂ hf₁ hf₂ hx₁ hx₂ hne
  subst h
  obtain ⟨hcol₁, hR₁, hC₁, hrow₁⟩ := props_A lam mu f₁ hf₁ hx₁
  obtain ⟨hcol₂, hR₂, hC₂, hrow₂⟩ := props_A lam mu f₂ hf₂ hx₂
  have hc₂ : AddMonoidAlgebra.coeff f₂ (mStarA (kapA lam mu) lam.natW) ≠ 0 := by
    intro h0
    apply hne
    exact vanishA f₂ hR₂ hC₂ (fun D hD => by
      rw [eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, h0, zero_mul])
  refine ⟨⟨AddMonoidAlgebra.coeff f₁ (mStarA (kapA lam mu) lam.natW) / AddMonoidAlgebra.coeff f₂ (mStarA (kapA lam mu) lam.natW), ?_⟩, ?_⟩
  · set c := AddMonoidAlgebra.coeff f₁ (mStarA (kapA lam mu) lam.natW) / AddMonoidAlgebra.coeff f₂ (mStarA (kapA lam mu) lam.natW) with hcdef
    have hg : f₁ - c • f₂ = 0 := by
      apply vanishA
      · intro x a b t hab hb
        have e1 := hR₁ x a b t hab hb
        have e2 := hR₂ x a b t hab hb
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro x l j c' hlj
        have e1 := hC₁ x l j c' hlj
        have e2 := hC₂ x l j c' hlj
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro D hD
        rw [map_sub, smul_eval, eval_D_A (kapA lam mu) lam.natW f₁ hcol₁ hrow₁ D hD,
          eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, hcdef]
        field_simp
        ring
    exact sub_eq_zero.mp hg
  · have hmS : mStarA (kapA lam mu) lam.natW ∈ f₂.support := mem_support_iff.mpr hc₂
    have hmu : ∀ a : Fin n, ((kapA lam mu a : ℕ) : ℤ) + lam.detShift = mu.w a := by
      intro a
      have hrd := fixed_rowDeg_A lam mu f₂ hx₂ _ hmS a
      have hsum : ∑ s, mStarA (kapA lam mu) lam.natW (Fin.castSucc a, s) = kapA lam mu a := by
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hsum] at hrd
      exact hrd
    have hleA : ∀ a : Fin n, kapA lam mu a ≤ lam.natW (Fin.castSucc a) := by
      intro a
      have hcs : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) = lam.natW (Fin.castSucc a) := by
        rw [← lhwline_weight_col, hcol₂ hc₂]
      have hcs2 : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) =
          kapA lam mu a + (lam.natW (Fin.castSucc a) - kapA lam mu a) := by
        rw [Fin.sum_univ_castSucc]
        simp [Finset.sum_ite_eq']
      omega
    intro i
    have hcast : (⟨i.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc i := Fin.ext rfl
    have hnat := natW_add_A lam (Fin.castSucc i)
    have h1 := hmu i
    have h2 := hleA i
    constructor
    · rw [hcast]
      omega
    · by_cases hi : i.val + 1 < n
      · have hcast' : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i.val + 1, hi⟩ := Fin.ext rfl
        have h3 := eps_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ hR₂ hC₂ hc₂ i ⟨i.val + 1, hi⟩ rfl
          (hleA ⟨i.val + 1, hi⟩)
        have hnat' := natW_add_A lam (Fin.castSucc ⟨i.val + 1, hi⟩)
        rw [hcast']
        omega
      · have hlast : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
        have hds : lam.w (Fin.last n) = lam.detShift := by
          unfold DomWeight.detShift
          rw [dite_eq_left (by omega)]
          congr 1
        rw [hlast, hds]
        omega

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem fixed_line_exists : FixedLine :=
  fixedLine_proof_A

end PI.WGB
