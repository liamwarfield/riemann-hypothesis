module

public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantLinearProduct.OfFnProdSmul
open Matrix Finset

namespace PI.QnCovLinW

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem ofFn_prod_sum {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ofFn_prod_sum t (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv]

theorem ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ofFn_prod_smul t (fun k => r k.succ) (fun k => x k.succ), Fin.prod_univ_succ,
      smul_mul_smul_comm]

theorem tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) (a b : Fin n) :
    Tm (Econj E P Q) u a b = ∑ x : Fin n × Fin n, (P x.1 a * Q b x.2) • Tm E u x.1 x.2 := by
  have hQP : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have h1 := congrFun (congrFun h b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from Finset.sum_congr rfl fun c _ => mul_comm _ _, h1]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  simp only [Tm, Econj, smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_smul, hQP]
  split_ifs <;> simp

theorem qnCovLin : PI.QnCovLin := by
  intro A _ _ n t E P Q hQP a b u
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Econj E P Q) (u - (k : ℂ)) (a (σ k)) (b k)).prod =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod := by
    intro σ
    simp only [tm_conj E P Q hQP]
    rw [ofFn_prod_sum]
    have hs : ∀ c : Fin t → Fin n × Fin n,
        (List.ofFn fun k => (P (c k).1 (a (σ k)) * Q (b k) (c k).2) • Tm E (u - (k : ℂ)) (c k).1 (c k).2).prod =
        (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod)
          (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n) c) := by
      intro c
      rw [ofFn_prod_smul, Finset.prod_mul_distrib]
      rfl
    rw [Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)) _
      (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod) hs,
      Fintype.sum_prod_type]
  have reidx : ∀ σ : Equiv.Perm (Fin t),
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ k, P (c k) (a k)) * ∏ k, Q (b k) (d k)) •
        (((Equiv.Perm.sign σ : ℤ) : A) *
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c (σ k)) (d k)).prod) := by
    intro σ
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, id]
    have hp : ∏ k, P (c (σ k)) (a (σ k)) = ∏ k, P (c k) (a k) := Equiv.prod_comp σ (fun k => P (c k) (a k))
    rw [mul_smul_comm, hp]
  simp only [qminor, key, Finset.mul_sum]
  simp only [reidx, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

end PI.QnCovLinW
end

theorem covariant_linear : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantDeterminantScaling.IntCastMulEqSmul
open Matrix Finset

noncomputable section

namespace PI.QnCovDetW

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {n : ℕ}
    (g : (Fin n → Fin n) → M) (hg : ∀ c, ¬ Function.Injective c → g c = 0) :
    ∑ c, g c = ∑ σ : Equiv.Perm (Fin n), g σ := by
  classical
  have h2 : ∑ σ : Equiv.Perm (Fin n), g σ = ∑ c ∈ Finset.univ.filter Function.Injective, g c := by
    refine Finset.sum_nbij (fun σ => (σ : Fin n → Fin n)) (fun σ _ => by simpa using σ.injective)
      (by intro a _ b _ h; exact DFunLike.coe_injective h) (by
        intro c hc
        have hc' : Function.Injective c := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
        exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hc'),
          Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩) (fun _ _ => rfl)
  rw [h2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · exact hg c h

theorem intCast_mul_eq_smul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) :
    (z : A) * x = (z : ℂ) • x := by
  rw [Algebra.smul_def, map_intCast]

private theorem qminor_rowperm_lemma {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) (π : Equiv.Perm (Fin t)) :
    qminor E (a ∘ π) b u = ((Equiv.Perm.sign π : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  have hs : ((Equiv.Perm.sign π : ℤ) : A) * ((Equiv.Perm.sign π : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply]
  rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, ← mul_assoc, hs, one_mul]

private theorem qminor_colperm_lemma_2 {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (a : Fin (m + 1) → Fin n) (u : ℂ) (τ : Equiv.Perm (Fin (m + 1))) :
    ∀ b : Fin (m + 1) → Fin n, qminor E a (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  have hcl : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top τ
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro b
    rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne]
    simp
  | one =>
    intro b
    simp
  | mul x y _ _ hx hy =>
    intro b
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul,
      mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul, mul_assoc]

theorem qminor_perm_perm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (σ τ : Equiv.Perm (Fin n)) (u : ℂ) :
    qminor E σ τ u =
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) • qdet E u := by
  rcases n with _ | m
  · have hσ : σ = 1 := Equiv.ext fun i => i.elim0
    have hτ : τ = 1 := Equiv.ext fun i => i.elim0
    subst hσ hτ
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, mul_one, one_smul, Equiv.Perm.coe_one]
    rfl
  · have h1 := qminor_rowperm_lemma E id (⇑τ) u σ
    have h2 := qminor_colperm_lemma_2 E hE id u τ id
    simp only [Function.id_comp] at h1 h2
    rw [h1, h2, intCast_mul_eq_smul, intCast_mul_eq_smul, smul_smul]
    rfl

theorem sum_sign_prod_left {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k = P.det := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]

theorem sum_sign_prod_right {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) :
    ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) = Q.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Matrix.transpose_apply]

theorem qnCovDet_of_lin (h : PI.QnCovLin) : PI.QnCovDet := by
  intro A _ _ n E P Q hE hQP hPQ u
  have hrep : ∀ c : Fin n → Fin n, ¬ Function.Injective c → ∃ p q, p ≠ q ∧ c p = c q := by
    intro c hc
    by_contra hne
    push_neg at hne
    exact hc (fun p q hpq => by_contra fun h => hne p q h hpq)
  have hrow : ∀ c d : Fin n → Fin n, ¬ Function.Injective c → qminor E c d u = 0 := by
    intro c d hc
    obtain ⟨p, q, hpq, hcq⟩ := hrep c hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq hcq
  have hcol : ∀ c d : Fin n → Fin n, ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hdq⟩ := hrep d hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hpq hdq
  have key : qdet (Econj E P Q) u = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k) * (((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k))) • qdet E u := by
    rw [show qdet (Econj E P Q) u = qminor (Econj E P Q) id id u from rfl, h A n n E P Q hQP id id u,
      sum_fun_eq_sum_perm]
    · refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [sum_fun_eq_sum_perm]
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [qminor_perm_perm E hE σ τ u, smul_smul]
        congr 1
        try simp only [id_eq]
        ring
      · intro d hd
        rw [hcol _ d hd, smul_zero]
    · intro c hc
      exact Finset.sum_eq_zero (fun d _ => by rw [hrow c d hc, smul_zero])
  rw [key]
  simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_mul_sum, sum_sign_prod_left, sum_sign_prod_right, ← Matrix.det_mul, hPQ,
    Matrix.det_one, one_smul]

end PI.QnCovDetW
end
end

theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.SkipOneEqSuccAbove
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.InjDecomp
open Finset

namespace PI.QnCovHatW

theorem inj_decomp {m : ℕ} (c : Fin m → Fin (m + 1)) (hc : Function.Injective c) :
    ∃ i : Fin (m + 1), ∃ σ : Equiv.Perm (Fin m), c = i.succAbove ∘ σ := by
  classical
  have hex : ∃ i, i ∉ Set.range c := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective c := fun y => h y
    have := Fintype.card_le_of_surjective c hs
    simp at this
  obtain ⟨i, hi⟩ := hex
  have hne : ∀ x, c x ≠ i := fun x hx => hi ⟨x, hx⟩
  choose f hf using fun x => Fin.exists_succAbove_eq (hne x)
  have finj : Function.Injective f := by
    intro x y hxy
    apply hc
    rw [← hf x, ← hf y, hxy]
  refine ⟨i, Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), ?_⟩
  funext x
  simp [hf]

theorem decomp_unique {m : ℕ} {i i' : Fin (m + 1)} {σ σ' : Equiv.Perm (Fin m)}
    (h : i.succAbove ∘ σ = i'.succAbove ∘ σ') : i = i' ∧ σ = σ' := by
  have hi : i = i' := by
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    have hh := congrFun h (σ'.symm z)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at hh
    rw [hz] at hh
    exact Fin.succAbove_ne _ _ hh
  subst hi
  exact ⟨rfl, Equiv.ext fun x => Fin.succAbove_right_injective (congrFun h x)⟩

theorem alt_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ}
    (g : (Fin m → Fin (m + 1)) → M)
    (hskew : ∀ c (σ : Equiv.Perm (Fin m)), g (c ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • g c)
    (hzero : ∀ c, ¬ Function.Injective c → g c = 0)
    (w : (Fin m → Fin (m + 1)) → ℂ) :
    ∑ c, w c • g c =
      ∑ i : Fin (m + 1),
        (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * w (i.succAbove ∘ σ)) • g i.succAbove := by
  classical
  have h1 : ∑ p : Fin (m + 1) × Equiv.Perm (Fin m),
      w (p.1.succAbove ∘ p.2) • g (p.1.succAbove ∘ p.2) = ∑ c, w c • g c := by
    apply Finset.sum_of_injOn (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => p.1.succAbove ∘ p.2)
    · intro p _ q _ hpq
      obtain ⟨h1, h2⟩ := decomp_unique hpq
      exact Prod.ext h1 h2
    · intro p _
      simp
    · intro c _ hc
      have hni : ¬ Function.Injective c := by
        intro hinj
        obtain ⟨i, σ, rfl⟩ := inj_decomp c hinj
        exact hc ⟨(i, σ), by simp, rfl⟩
      simp [hzero c hni]
    · intro p _
      rfl
  rw [← h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hskew i.succAbove σ, smul_smul, mul_comm]

end PI.QnCovHatW
end

open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q

namespace PI.QnCovHatW

theorem skip_one_eq_succAbove {m : ℕ} (i : Fin (m + 1)) (j : Fin m) : skip1 (t := m + 1) i j = i.succAbove j := by
  apply Fin.ext
  unfold skip1
  by_cases h : (j : ℕ) < (i : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castSucc]; omega)]
    rfl

theorem qminor_skip {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (i j : Fin (m + 1)) (u : ℂ) :
    qminor E (skip1 i) (skip1 j) u = qminor (t := m) E i.succAbove j.succAbove u := by
  have h1 : (fun k : Fin m => skip1 (t := m + 1) i k) = i.succAbove := funext (skip_one_eq_succAbove i)
  have h2 : (fun k : Fin m => skip1 (t := m + 1) j k) = j.succAbove := funext (skip_one_eq_succAbove j)
  rw [← h1, ← h2]

theorem int_smul_eq {A : Type} [Ring A] [Algebra ℂ A] (k : ℤ) (x : A) :
    ((k : ℂ)) • x = (k : A) * x := by
  rw [Algebra.smul_def, map_intCast]

theorem swap4 {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := by
  calc ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i, ∑ i', ∑ j', ∑ j, f i j i' j' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ i', ∑ i, ∑ j', ∑ j, f i j i' j' := Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm

theorem det_sub_eq {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i' i : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, P ((i'.succAbove ∘ σ) k) (i.succAbove k) =
      (P.submatrix i'.succAbove i.succAbove).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_sub_eq' {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j j' : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, Q (j.succAbove k) ((j'.succAbove ∘ σ) k) =
      (Q.submatrix j.succAbove j'.succAbove).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem scal {m : ℕ} (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hPQ : P * Q = 1)
    (a β : Fin (m + 1) → ℂ) (i' j' : Fin (m + 1)) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β ᵥ* P) i * (Q *ᵥ a) j) *
          ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
  have hsign : ∀ i j : Fin (m + 1), ((-1 : ℂ)) ^ ((i : ℕ) + (j : ℕ)) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) := by
    intro i j
    rw [← pow_add, ← pow_add]
    have h : (i' : ℕ) + j' + ((i' : ℕ) + i + ((j : ℕ) + j')) = ((i : ℕ) + j) + 2 * ((i' : ℕ) + j') := by ring
    rw [h, pow_add (-1 : ℂ) ((i : ℕ) + (j : ℕ)), pow_mul]
    norm_num
  have hX : ∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
      (P.submatrix i'.succAbove i.succAbove).det) = P.det * β i' := by
    have h1 : ∀ i : Fin (m + 1), (-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
        (P.submatrix i'.succAbove i.succAbove).det = P.adjugate i i' :=
      fun i => (Matrix.adjugate_fin_succ_eq_det_submatrix P i i').symm
    simp_rw [h1]
    have h2 : ∑ i, (β ᵥ* P) i * P.adjugate i i' = (β ᵥ* P ᵥ* P.adjugate) i' := rfl
    rw [h2, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    first
    | (rw [Matrix.vecMul_smul, Matrix.vecMul_one]; rfl)
    | simp [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm]
  have hY : ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
      (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j = Q.det * a j' := by
    have h1 : ∀ j : Fin (m + 1), (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
        (Q.submatrix j.succAbove j'.succAbove).det = Q.adjugate j' j :=
      fun j => (Matrix.adjugate_fin_succ_eq_det_submatrix Q j' j).symm
    simp_rw [h1]
    have h2 : ∑ j, Q.adjugate j' j * (Q *ᵥ a) j = (Q.adjugate *ᵥ (Q *ᵥ a)) j' := rfl
    rw [h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    first
    | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
    | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  calc _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) *
        ((∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
          (P.submatrix i'.succAbove i.succAbove).det)) *
        (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
          (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsign i j]
        ring
    _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
        rw [hX, hY]
        linear_combination (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' * hdet

theorem qnCovHat_of_lin (hL : PI.QnCovLin) : PI.QnCovHat := by
  intro A _ _ n E P Q hE hQP hPQ u a β
  cases n with
  | zero => simp [chatA]
  | succ m =>
  have rskew : ∀ (d c : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E (c ∘ σ) d u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro d c σ
    rw [int_smul_eq]
    exact quantumMinorRowSkew_holds A (m + 1) m E c d σ u
  have rzero : ∀ (d c : Fin m → Fin (m + 1)), ¬ Function.Injective c → qminor E c d u = 0 := by
    intro d c hc
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hne hpq
  have cskew : ∀ (c d : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E c (d ∘ σ) u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro c d σ
    rw [int_smul_eq]
    exact quantumMinorColSkew_holds A (m + 1) m E hE c d σ u
  have czero : ∀ (c d : Fin m → Fin (m + 1)), ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hne hpq
  have key : ∀ i j : Fin (m + 1), qminor (Econj E P Q) i.succAbove j.succAbove u =
      ∑ i' : Fin (m + 1), ∑ j' : Fin (m + 1),
        ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) •
          qminor E i'.succAbove j'.succAbove u := by
    intro i j
    rw [hL A (m + 1) m E P Q hQP i.succAbove j.succAbove u]
    simp_rw [mul_smul]
    simp_rw [← Finset.smul_sum]
    have inner : ∀ c : Fin m → Fin (m + 1),
        ∑ d : Fin m → Fin (m + 1), (∏ k, Q (j.succAbove k) (d k)) • qminor E c d u =
          ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u := by
      intro c
      rw [alt_sum (fun d => qminor E c d u) (cskew c) (czero c)]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [det_sub_eq']
    simp_rw [inner]
    rw [alt_sum (fun c => ∑ j' : Fin (m + 1),
        (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u) ?_ ?_]
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [det_sub_eq, Finset.smul_sum]
    · intro c σ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [rskew, smul_comm]
    · intro c hc
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [rzero _ c hc, smul_zero]
  simp only [chatA, qminor_skip]
  simp_rw [key, Finset.smul_sum, smul_smul]
  rw [swap4]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  simp_rw [← Finset.sum_smul]
  rw [scal P Q hPQ a β i' j']

end PI.QnCovHatW
end

theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
theorem qnYLeibniz : Formalism.FourierDecayAlt.Q.YLeibniz := QnYLeibnizW.y_operator_leibniz_rule
end
