module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OfFnProdSmul
open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL

theorem ofFn_prod_sum {A : Type*} [Ring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (F : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, F k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => F k (c k)).prod := by
  intro t
  induction t with
  | zero => intro F; simp
  | succ t ih =>
    intro F
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => F k.succ), Finset.sum_mul_sum]
    first
    | (rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Fin.consEquiv])
    | (rw [← (Equiv.piFinSucc t ι).symm.sum_comp, Fintype.sum_prod_type]
       simp [List.ofFn_succ, Equiv.piFinSucc])

theorem ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (w : Fin t → ℂ) (X : Fin t → A),
      (List.ofFn fun k => w k • X k).prod = (∏ k, w k) • (List.ofFn X).prod := by
  intro t
  induction t with
  | zero => intro w X; simp
  | succ t ih =>
    intro w X
    rw [List.ofFn_succ, List.prod_cons, ih (fun k => w k.succ) (fun k => X k.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring

theorem tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ) (i j : Fin n) :
    Tm (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) x i j =
      ∑ p : Fin n × Fin n, (P p.1 i * Q j p.2) • Tm E x p.1 p.2 := by
  simp only [Tm]
  simp only [smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  have hsum : ∑ c, P c i * Q j c = (Q * P) j i := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [hsum, hQP, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem sum_perm_mul_sum_prod_smul_eq_sum_sum {A : Type*} [Ring A] [Algebra ℂ A] {t n : ℕ}
    (s : Equiv.Perm (Fin t) → A) (w1 : Fin n → Fin t → ℂ) (w2 : Fin t → Fin n → ℂ)
    (G : (Fin t → Fin n) → (Fin t → Fin n) → A) :
    ∑ σ : Equiv.Perm (Fin t), s σ * ∑ cd : Fin t → Fin n × Fin n,
        (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        ∑ σ : Equiv.Perm (Fin t), s σ * G (fun k => c (σ k)) d := by
  have h1 : ∀ σ : Equiv.Perm (Fin t), ∑ cd : Fin t → Fin n × Fin n,
      (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        G (fun k => c (σ k)) d := by
    intro σ
    rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.arrowCongr_apply, Equiv.symm_symm,
      Equiv.coe_refl, Equiv.coe_fn_symm_mk, Function.comp_apply, id]
    congr 1
    rw [Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp σ (fun j => w1 (c j) j)
  simp only [h1, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]

theorem q_expansion : QExpand := by
  unfold QExpand
  intro A _ _ n t E P Q a b u hQP
  simp only [qminor]
  simp only [tm_conj E P Q hQP, ofFn_prod_sum, ofFn_prod_smul]
  exact sum_perm_mul_sum_prod_smul_eq_sum_sum (fun σ => ((Equiv.Perm.sign σ : ℤ) : A)) (fun x j => P x (a j))
    (fun k y => Q (b k) y) (fun c1 d => (List.ofFn fun k => Tm E (u - ((k : ℕ) : ℂ)) (c1 k) (d k)).prod)

end AAInvW
end
end

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem eI_inj (k r : ℕ) : Function.Injective (eI k r) := by
  unfold eI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  exact Fin.ext h1

theorem esI_inj (k r : ℕ) : Function.Injective (esI k r) := by
  unfold esI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  unfold keyS
  intro p q h
  simp only at h
  have hp := p.isLt
  have hq := q.isLt
  split_ifs at h <;> exact Fin.ext (by omega)

theorem strictMono_val_iff {m N : ℕ} (C : Fin m → Fin N) :
    StrictMono (fun l => (C l).val) ↔ StrictMono C :=
  ⟨fun h _ _ hab => h hab, fun h _ _ hab => h hab⟩

theorem not_inj {α β : Type*} {c : α → β} (hc : ¬ Function.Injective c) :
    ∃ p q, p ≠ q ∧ c p = c q := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨p, q, h, hne⟩ := hc
  exact ⟨p, q, hne, h⟩

theorem det_transpose_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp [Units.smul_def, zsmul_eq_mul, Matrix.transpose_apply]

theorem algebra_aa : AlgAA := by
  intro A _ _ k r m hm E P Q xi u hE hQP hP
  classical
  have hrow : ∀ D : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) (xR k r m hm) D u =
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u := by
    intro D
    rw [q_expansion A _ m E P Q _ D u hQP]
    simp only [mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show (∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (xR k r m hm j)) • (∏ j, Q (D j) (d j)) •
        qminor E c d u) = ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) •
        (∏ j, P (c j) (xR k r m hm j)) • qminor E c d u from
      Finset.sum_congr rfl (fun c _ => smul_comm _ _ _)]
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (eI k r) (eI_inj k r) P hP (fun c => qminor E c d u)
      (fun c hc => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hc
        exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq h)
  simp only [hrow]
  have h1 : ∀ D : Fin m → Fin (2 * r + k + 1),
      (if StrictMono D then (Matrix.of fun a l : Fin m => xi a (D l)).det •
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u else 0) =
      ∑ d : Fin m → Fin (2 * r + k + 1), (if StrictMono D then
        (Matrix.of fun a l : Fin m => xi a (D l)).det * ∏ j, Q (D j) (d j) else 0) •
          qminor E (xR k r m hm) d u := by
    intro D
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (fun i => i.val) Fin.val_injective (fun d => qminor E (xR k r m hm) d u)
    (fun d τ => quantumMinorColSkew_holds A _ m E hE (xR k r m hm) d τ u)
    (fun d hd => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hd
      exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE (xR k r m hm) d u p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp only [strictMono_val_iff]
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, Q d (C l) * xi a d) =
        (Matrix.of fun a d => xi a d) * (Matrix.of fun d l => Q d (C l)) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (fun i => i.val) Fin.val_injective]
    simp only [strictMono_val_iff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    split_ifs with hD
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => Q (D i) (C l)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

theorem algebra_aa_vector : AlgAAv := by
  intro A _ _ k r m hm E P Q eta v hE hQP hQ
  classical
  have hcol : ∀ B : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) B (sR k r m hm) v =
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v := by
    intro B
    rw [q_expansion A _ m E P Q B _ v hQP]
    simp only [mul_smul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (esI k r) (esI_inj k r) (fun i j => Q j i) hQ (fun d => qminor E c d v)
      (fun d hd => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hd
        exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d v p q hpq h)
  simp only [hcol]
  have h1 : ∀ B : Fin m → Fin (2 * r + k + 1),
      (if StrictMono (fun l => keyS k r (B l)) then (Matrix.of fun a l : Fin m => eta a (B l)).det •
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v else 0) =
      ∑ c : Fin m → Fin (2 * r + k + 1), (if StrictMono (fun l => keyS k r (B l)) then
        (Matrix.of fun a l : Fin m => eta a (B l)).det * ∏ j, P (c j) (B j) else 0) •
          qminor E c (sR k r m hm) v := by
    intro B
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (keyS k r) (keyS_inj k r) (fun c => qminor E c (sR k r m hm) v)
    (fun c τ => quantumMinorRowSkew_holds A _ m E c (sR k r m hm) τ v)
    (fun c hc => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hc
      exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c (sR k r m hm) v p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, P (C l) d * eta a d) =
        (Matrix.of fun a d => eta a d) * (Matrix.of fun d l => P (C l) d) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (keyS k r) (keyS_inj k r)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    split_ifs with hB
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => P (C l) (B i)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

end AAInvW
