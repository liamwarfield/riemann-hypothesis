module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.NatWAntiC
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.TransposeConjComm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.AevalScaleMonomial
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFRowActRight
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def iotaC (R : Type) [CommRing R] (n k : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks Y 0 0 1)

theorem iotaC_mul (R : Type) [CommRing R] (n k : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    iotaC R n k (A * B) = iotaC R n k A * iotaC R n k B := by
  rw [iotaC, iotaC, iotaC, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem iotaC_one (R : Type) [CommRing R] (n k : ℕ) : iotaC R n k 1 = 1 := by
  rw [iotaC, Matrix.fromBlocks_one, map_one]

theorem iotaC_map (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) R) : (iotaC R n k Y).map φ = iotaC S n k (Y.map φ) := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem iotaC_conj (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    iotaC ℂ n k Y.conjTranspose = (iotaC ℂ n k Y).conjTranspose := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

theorem iotaC_det (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : (iotaC ℂ n k Y).det = Y.det := by
  rw [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem iotaC_zero (R : Type) [CommRing R] (n : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    iotaC R n 0 Y = Y := by
  have hi : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i := fun i => by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  simp [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi]

open Formalism.REAL (fockF)

def fct {σ : Type} (m : σ →₀ ℕ) : ℂ := ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

theorem fockF_eq_sum {σ : Type} (p q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : ∀ m, p.coeff m ≠ 0 → q.coeff m ≠ 0 → m ∈ s) :
    fockF p q = ∑ m ∈ s, p.coeff m * star (q.coeff m) * fct m := by
  classical
  trans ∑ m ∈ p.support ∩ s, p.coeff m * star (q.coeff m) * fct m
  · unfold fockF fct
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro m hm hms
    by_cases hq : q.coeff m = 0
    · simp [hq]
    · exact absurd (Finset.mem_inter.mpr ⟨hm, hs m (MvPolynomial.mem_support_iff.mp hm) hq⟩) hms
  · apply Finset.sum_subset Finset.inter_subset_right
    intro m hm hms
    by_cases hp : p.coeff m = 0
    · simp [hp]
    · exact absurd (Finset.mem_inter.mpr ⟨MvPolynomial.mem_support_iff.mpr hp, hm⟩) hms

theorem fockF_add_left {σ : Type} (p p' q : MvPolynomial σ ℂ) :
    fockF (p + p') q = fockF p q + fockF p' q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support →
      fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m :=
    fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))
  rw [hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left,
    hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockF_smul_left {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF (c • p) q = c * fockF p q := by
  classical
  rw [fockF_eq_sum (c • p) q p.support (fun m h _ => by
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at h
        exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),
    fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_zero_left {σ : Type} (q : MvPolynomial σ ℂ) : fockF 0 q = 0 := by
  simp [fockF]

theorem fockF_add_right {σ : Type} (p q q' : MvPolynomial σ ℂ) :
    fockF p (q + q') = fockF p q + fockF p q' := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_right {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF p (c • q) = star c * fockF p q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_sum_left {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, x i) q = ∑ i ∈ s, fockF (x i) q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_left, ih]

theorem fockF_sum_right {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    fockF p (∑ i ∈ s, x i) = ∑ i ∈ s, fockF p (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, ih]

theorem fockF_lc {σ ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, a i • x i) (∑ j ∈ s, a j • x j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (x i) (x j) := by
  rw [fockF_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fockF_smul_left, fockF_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fockF_smul_right]
  ring

private theorem eq_zero_of_fockF_self_eq_zero {σ : Type} (p : MvPolynomial σ ℂ) (h : fockF p p = 0) : p = 0 := by
  classical
  by_contra hp
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hp)
  have hre : (fockF p p).re =
      ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    unfold fockF
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (p.coeff m * (starRingEnd ℂ) (p.coeff m) * _).re = _
    rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpos : 0 < ∑ m ∈ p.support, Complex.normSq (p.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) :=
    Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm))
      (Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _))) ⟨m, hm⟩
  rw [← hre, h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem lc_zero_of_gram {σ τ ι : Type} (s : Finset ι) (a : ι → ℂ) (xe : ι → MvPolynomial σ ℂ)
    (xf : ι → MvPolynomial τ ℂ) (K : ℂ)
    (hK : ∀ i j, fockF (xf i) (xf j) = K * fockF (xe i) (xe j))
    (h0 : ∑ i ∈ s, a i • xe i = 0) : ∑ i ∈ s, a i • xf i = 0 := by
  have hyy : fockF (∑ i ∈ s, a i • xf i) (∑ i ∈ s, a i • xf i) = 0 := by
    have he := fockF_lc s a xe
    rw [h0, fockF_zero_left] at he
    rw [fockF_lc]
    simp_rw [hK]
    calc _ = K * ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (xe i) (xe j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [← he, mul_zero]
  exact eq_zero_of_fockF_self_eq_zero _ hyy

theorem fockF_rowAct_right (r n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (p q : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF p (rowAct ℂ M q) = fockF (rowAct ℂ M.conjTranspose p) q := by
  rw [fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

def IsUU {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def matOf {n : ℕ} (x : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j)

theorem matOf_self {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : matOf (fun v => Y v.1 v.2) = Y := by
  ext i j; rfl

def hwAt {n : ℕ} (κ : Fin n → ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  eval (fun v => Y v.1 v.2) (hw ℂ le_rfl κ)

theorem rowAct_comp_apply {R : Type} [CommRing R] {r c : ℕ} (A B : Matrix (Fin r) (Fin r) R)
    (p : MvPolynomial (Fin r × Fin c) R) : rowAct R B (rowAct R A p) = rowAct R (A * B) p := by
  rw [Formalism.UG.P.wlocal_rowAct_mul]; rfl

theorem rowAct_one_apply {R : Type} [CommRing R] {r c : ℕ} (p : MvPolynomial (Fin r × Fin c) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) p = p := by
  rw [Formalism.UG.P.wlocal_rowAct_one]; rfl

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r c : ℕ}
    (A : Matrix (Fin r) (Fin r) R) (p : MvPolynomial (Fin r × Fin c) R) :
    map φ (rowAct R A p) = rowAct S (A.map φ) (map φ p) := by
  have : (map φ).comp (rowAct R (n := c) A).toRingHom =
      (rowAct S (n := c) (A.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rowAct]
    · intro v; simp [rowAct]
  exact congrArg (fun ψ => ψ p) this

theorem eval_aeval_self {σ : Type} (x : σ → ℂ) (g : σ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    eval x (aeval g p) = eval (fun v => eval x (g v)) p := by
  rw [aeval_eq_bind₁]; exact eval₂Hom_bind₁ _ _ _ _

section MC

variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)

def mcF (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ := fockF (rowAct ℂ (iotaC ℂ n k Y).transpose f) f

def genY (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) := Matrix.of fun i j => X (i, j)

def mcP : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ m ∈ f.support, (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)).coeff m * C (star (f.coeff m) * fct m)

theorem eval_matrixCoeffPoly (x : Fin n × Fin n → ℂ) : eval x (mcP f) = mcF f (matOf x) := by
  have hmap : map (eval x) (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)) = rowAct ℂ (iotaC ℂ n k (matOf x)).transpose f := by
    rw [map_rowAct, map_map, Matrix.transpose_map, iotaC_map]
    have h1 : (eval x).comp (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = RingHom.id ℂ :=
      RingHom.ext fun a => by simp
    have h2 : (genY n).map (eval x) = matOf x := by ext i j; simp [genY, matOf]
    rw [h1, map_id, h2]
  unfold mcP mcF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, fockF_eq_sum _ f f.support (fun m _ h => mem_support_iff.mpr h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, ← coeff_map, hmap, mul_assoc]

variable {f}

theorem mcF_mulU (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (Y U : Matrix (Fin n) (Fin n) ℂ) (hUU : IsUU U) : mcF f (Y * U) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hU U hUU]

theorem mcF_Lmul (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (L Y : Matrix (Fin n) (Fin n) ℂ) (hL : IsUU L.conjTranspose) : mcF f (L * Y) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, fockRowAdj (n + k) (n + k)]
  have : ((iotaC ℂ n k L).transpose).conjTranspose = (iotaC ℂ n k L.conjTranspose).transpose := by
    rw [iotaC_conj]; ext i j; simp
  rw [this, hU _ hL]

theorem mcF_diag {κ : Fin n → ℕ}
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂˣ) :
    mcF f (Y * Matrix.diagonal fun i => (t i : ℂ)) = (∏ i, (t i : ℂ) ^ κ i) * mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hT t, map_smul, fockF_smul_left]

theorem mcF_one : mcF f 1 = fockF f f := by
  unfold mcF
  rw [iotaC_one, Matrix.transpose_one, rowAct_one_apply]

theorem isUU_E (l j : Fin n) (hlj : l < j) (c : ℂ) : IsUU (Formalism.UG.P.wlocal_E l j c) := by
  refine ⟨fun i j' h => ?_, fun i => ?_⟩
  · simp only [Formalism.UG.P.wlocal_E]
    rw [if_neg (by intro e; subst e; exact lt_irrefl _ h), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_asymm h hlj
  · simp only [Formalism.UG.P.wlocal_E, if_true]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hlj

theorem isUU_E_conj (a b : Fin n) (hab : a < b) (c : ℂ) :
    IsUU (Formalism.UG.P.wlocal_E b a c).conjTranspose := by
  refine ⟨fun i j' h => ?_, fun i => ?_⟩
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E]
    rw [if_neg (by intro e; subst e; exact lt_irrefl _ h), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_asymm h hab
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E, if_true]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h2⟩; exact lt_irrefl _ (h2 ▸ hab)

theorem colAdd_matrixCoeffPoly (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (l j : Fin n) (hlj : l < j) (c : ℂ) : colAdd ℂ l j c (mcP f) = mcP f := by
  apply MvPolynomial.funext
  intro x
  rw [colAdd, eval_aeval_self]
  have key : (fun v : Fin n × Fin n => eval x (if v.2 = j then X v + C c * X (v.1, l) else X v)) =
      fun v => (matOf x * Formalism.UG.P.wlocal_E l j c) v.1 v.2 := by
    funext v
    simp only [matOf, Matrix.mul_apply, Matrix.of_apply, Formalism.UG.P.wlocal_E, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : v.2 = j
    · simp [h, mul_comm] <;> rw [← h]
    · simp [h]
  rw [key, eval_matrixCoeffPoly, matOf_self, mcF_mulU hU _ _ (isUU_E l j hlj c), ← eval_matrixCoeffPoly]

theorem rowDiv_matrixCoeffPoly_eq_zero (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (a b : Fin n) (hab : a < b) (kk : ℕ) (hk : 1 ≤ kk) : rowDiv ℂ a b kk (mcP f) = 0 := by
  have hpt : ∀ c : ℂ, rowAct ℂ (Formalism.UG.P.wlocal_E b a c) (mcP f) = mcP f := by
    intro c
    apply MvPolynomial.funext
    intro x
    rw [rowAct, eval_aeval_self]
    have key : (fun v : Fin n × Fin n => eval x (∑ b' : Fin n, C (Formalism.UG.P.wlocal_E b a c v.1 b') * X (b', v.2))) =
        fun v => (Formalism.UG.P.wlocal_E b a c * matOf x) v.1 v.2 := by
      funext v
      simp [matOf, Matrix.mul_apply]
    rw [key, eval_matrixCoeffPoly, matOf_self, mcF_Lmul hU _ _ (isUU_E_conj a b hab c), ← eval_matrixCoeffPoly]
  set q := rowGen ℂ a b (mcP f) - Polynomial.C (mcP f) with hq
  have hroot : ∀ c : ℂ, q.IsRoot (C c) := by
    intro c
    rw [Polynomial.IsRoot, hq, Polynomial.eval_sub, Formalism.UG.P.wlocal_eval_rowGen b a c (mcP f), hpt,
      Polynomial.eval_C, sub_self]
  have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q
    (Set.infinite_of_injective_forall_mem (MvPolynomial.C_injective (Fin n × Fin n) ℂ) hroot)
  have : rowGen ℂ a b (mcP f) = Polynomial.C (mcP f) := sub_eq_zero.mp hq0
  rw [rowDiv, this, Polynomial.coeff_C, if_neg (by omega)]

theorem aeval_scale_monomial (t : Fin n → ℂ) (m : Fin n × Fin n →₀ ℕ) (a : ℂ) :
    aeval (fun v : Fin n × Fin n => C (t v.2) * X v) (monomial m a) =
      monomial m (a * m.prod fun v e => t v.2 ^ e) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq, map_mul]
  rw [map_finsuppProd]
  simp only [map_pow]
  ring

theorem coeff_scale (t : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) (m : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v : Fin n × Fin n => C (t v.2) * X v) P) m = (m.prod fun v e => t v.2 ^ e) * AddMonoidAlgebra.coeff P m := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro m' a
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · intro p q hp hq
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem isWH_of_scale (κ : Fin n → ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ t : Fin n → ℂˣ, aeval (fun v : Fin n × Fin n => C ((t v.2 : ℂ)) * X v) P =
      C (∏ i, (t i : ℂ) ^ κ i) * P) :
    IsWeightedHomogeneous (colW n n) P κ := by
  classical
  intro m hm
  funext s
  let t : Fin n → ℂˣ := fun i => if i = s then Units.mk0 2 two_ne_zero else 1
  have h0 := coeff_scale (fun i => (t i : ℂ)) P m
  rw [h t, coeff_C_mul] at h0
  have h2 := (mul_right_cancel₀ hm h0).symm
  have ht : ∀ i, (t i : ℂ) = if i = s then 2 else 1 := by
    intro i; simp only [t]; split_ifs <;> simp
  simp only [ht, Finsupp.prod, ite_pow, one_pow] at h2
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum,
    Finset.prod_ite_eq' Finset.univ s, if_pos (Finset.mem_univ _)] at h2
  have h3 : ∑ v ∈ m.support with v.2 = s, m v = κ s := by
    have h4 : ((2 ^ (∑ v ∈ m.support with v.2 = s, m v) : ℕ) : ℂ) = ((2 ^ κ s : ℕ) : ℂ) := by
      push_cast; exact h2
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h4)
  rw [← h3, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [colW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hv : v.2 = s
  · simp [hv]
  · simp [hv, Ne.symm hv]

theorem eval_lpMinor_one (s : ℕ) (h1 h2 : s ≤ n) :
    eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (lpMinor ℂ s h1 h2) = 1 := by
  rw [lpMinor, RingHom.map_det]
  have : (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)) = 1 := by
    ext p q
    simp [Matrix.one_apply, Fin.castLE_inj]
  rw [this, Matrix.det_one]

theorem hwAt_one (κ : Fin n → ℕ) : hwAt κ 1 = 1 := by
  unfold hwAt hw
  rw [map_prod]
  simp only [map_pow, eval_lpMinor_one, one_pow, Finset.prod_const_one]

theorem mc_hw (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) : mcF f Y = fockF f f * hwAt κ Y := by
  have hhom : IsWeightedHomogeneous (colW n n) (mcP f) κ := by
    apply isWH_of_scale
    intro t
    apply MvPolynomial.funext
    intro x
    rw [eval_aeval_self, eval_mul, eval_C, eval_matrixCoeffPoly, eval_matrixCoeffPoly]
    have : matOf (fun v : Fin n × Fin n => eval x (C ((t v.2 : ℂ)) * X v)) =
        matOf x * Matrix.diagonal fun i => (t i : ℂ) := by
      ext i j; simp [matOf, Matrix.mul_diagonal, mul_comm]
    rw [this, mcF_diag hT]
  have hmem : mcP f ∈ dualWeyl ℂ n n κ :=
    (dualWeylPoint ℂ n n κ (mcP f)).mpr ⟨hhom, fun l j hlj c => colAdd_matrixCoeffPoly hU l j hlj c⟩
  obtain ⟨c, hc⟩ := hwLine ℂ n n le_rfl κ hκ (mcP f) hmem
    (fun a b hab kk hk => rowDiv_matrixCoeffPoly_eq_zero hU a b hab kk hk)
  have h1 : eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (mcP f) = fockF f f := by
    rw [eval_matrixCoeffPoly, matOf_self, mcF_one]
  rw [hc, smul_eval] at h1
  have h1' : c = fockF f f := by
    have := hwAt_one κ
    unfold hwAt at this
    rw [this, mul_one] at h1
    exact h1
  rw [← matOf_self Y, ← eval_matrixCoeffPoly, hc, smul_eval, h1']
  rfl

end MC

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem transpose_conj_comm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.transpose.conjTranspose = M.conjTranspose.transpose := by
  ext i j; simp

theorem gram_of {n k : ℕ} {f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ} (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (g g' : Matrix (Fin n) (Fin n) ℂ) :
    fockF (rowAct ℂ (iotaC ℂ n k g).transpose f) (rowAct ℂ (iotaC ℂ n k g').transpose f) =
      fockF f f * hwAt κ (g'.conjTranspose * g) := by
  have e1 : (iotaC ℂ n k g).transpose * (iotaC ℂ n k g').transpose.conjTranspose =
      (iotaC ℂ n k (g'.conjTranspose * g)).transpose := by
    rw [iotaC_mul, iotaC_conj, Matrix.transpose_mul, transpose_conj_comm]
  rw [fockF_rowAct_right, rowAct_comp_apply, e1]
  exact mc_hw κ hκ hU hT _

theorem eval_lpMinor_top {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) (h1 h2 : s ≤ n) (hs : s = n) :
    eval (fun v : Fin n × Fin n => Z v.1 v.2) (lpMinor ℂ s h1 h2) = Z.det := by
  subst hs
  rw [lpMinor, RingHom.map_det]
  congr 1
  ext p q
  simp

theorem hwAt_shift {n : ℕ} (κ' : Fin n → ℕ) (d : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hwAt (fun i => κ' i + d) Z = Z.det ^ d * hwAt κ' Z := by
  cases n with
  | zero => simp [hwAt, hw, Matrix.det_isEmpty]
  | succ m =>
    unfold hwAt hw
    simp only [map_prod, map_pow]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ ν : Fin (m + 1) → ℕ, nuNext ν (Fin.last m) = 0 := by intro ν; simp [nuNext]
    have hmid : ∀ i : Fin m, (κ' i.castSucc + d) - nuNext (fun i => κ' i + d) i.castSucc =
        κ' i.castSucc - nuNext κ' i.castSucc := by
      intro i
      have := i.isLt
      simp only [nuNext, Fin.coe_castSucc]
      split_ifs <;> omega
    simp only [hlast, hmid, Nat.sub_zero]
    rw [eval_lpMinor_top Z _ _ _ (by simp)]
    ring

theorem detPow_eq {N : ℕ} (g : GL (Fin N) ℂ) (c : ℤ) :
    detPow ℂ N g c = ((g : Matrix (Fin N) (Fin N) ℂ).det) ^ c := by
  simp [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem sqAct_eq {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g f = ((g : Matrix (Fin N) (Fin N) ℂ).det ^ lam.detShift) •
      rowAct ℂ (g : Matrix (Fin N) (Fin N) ℂ).transpose f := by
  rw [sqAct, detPow_eq]

theorem sqAct_mulC {N : ℕ} (lam : DomWeight N) (g h : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam (g * h) f = sqAct ℂ N lam g (sqAct ℂ N lam h f) := by
  simp only [sqAct_eq, map_smul, smul_smul, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul,
    rowAct_comp_apply, Matrix.det_mul]
  rw [mul_zpow]

theorem sqAct_oneC {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam 1 f = f := by
  simp [sqAct_eq, rowAct_one_apply]

def sqLC (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add (f := _), smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem sqLC_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLC N lam g f = sqAct ℂ N lam g f := rfl

theorem embGL_coe (n : ℕ) (g : GL (Fin n) ℂ) :
    ((PI.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      iotaC ℂ n 1 g := by
  simp [PI.embGL, PI.blkHom, iotaC]

theorem fixed_data {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ) (c : ℤ) (w : Fin n → ℤ)
    (κ : Fin n → ℕ) (hwκ : ∀ i, (κ i : ℤ) + c = w i)
    (hU0 : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) →
      (∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) →
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ c) • rowAct ℂ (iotaC ℂ n k g).transpose f = f)
    (hT0 : ∀ t : Fin n → ℂˣ, ((∏ i, (t i : ℂ)) ^ c) •
      rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f = (∏ i, (t i : ℂ) ^ w i) • f) :
    (∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f) ∧
    (∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f) := by
  refine ⟨fun u hu => ?_, fun t => ?_⟩
  · have hdet : u.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j h => hu.1 i j h)]
      simp [hu.2]
    have := hU0 (Matrix.GeneralLinearGroup.mkOfDetNeZero u (by rw [hdet]; exact one_ne_zero))
      (fun i j h => hu.1 i j h) (fun i => hu.2 i)
    simpa [hdet] using this
  · have h0 := hT0 t
    have hne : (∏ i, (t i : ℂ)) ^ c ≠ 0 := zpow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => (t i).ne_zero)
    have hw : (∏ i, (t i : ℂ) ^ w i) = (∏ i, (t i : ℂ) ^ κ i) * (∏ i, (t i : ℂ)) ^ c := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hwκ i, zpow_add₀ (t i).ne_zero, zpow_natCast]
    rw [hw, mul_comm, ← smul_smul] at h0
    exact smul_right_injective _ hne h0

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem natW_antiC {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem twist_id (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (cF cE : ℤ) (d : ℕ) (hc : cE = cF + d) :
    a ^ cF * star (b ^ cF) * (star b * a) ^ d = a ^ cE * star (b ^ cE) := by
  subst hc
  rw [star_zpow₀, star_zpow₀, zpow_add₀ ha, zpow_add₀ (star_ne_zero.mpr hb), zpow_natCast, zpow_natCast,
    mul_pow]
  ring

def veC (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  sqAct ℂ n mu g (extremal ℂ n mu)

def vfC (n : ℕ) (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (g : GL (Fin n) ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ :=
  sqAct ℂ (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g) f

theorem realize_C (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (n : ℕ) (lam : DomWeight (n + 1))
    (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) (hf : f ∈ nablaSq ℂ (n + 1) lam)
    (hfix : IsFixedW rfl lam mu f) (hne : f ≠ 0) :
    ∃ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ,
      IsEqv rfl mu lam φ ∧ φ (extremal ℂ n mu) = f := by
  have hI : Interlace rfl lam mu := (ha n (n + 1) rfl lam mu f f hf hf hfix hfix hne).2
  have heM : extremal ℂ n mu ∈ nablaSq ℂ n mu := hwMem ℂ n n le_rfl mu.natW (natW_antiC mu)
  have heN : extremal ℂ n mu ≠ 0 := hwNe ℂ n n le_rfl mu.natW

  have hge : 0 < n → lam.detShift ≤ mu.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have e1 : ∀ j : Fin (n + 1), j.val = n → lam.w j = lam.w ⟨n + 1 - 1, by omega⟩ :=
      fun j hj => congrArg lam.w (Fin.ext (by simp only; omega))
    rw [e1 _ (by simp only; omega)] at h1
    simp only [DomWeight.detShift, dif_pos hn, dif_pos (Nat.succ_pos n)]
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (mu.detShift - lam.detShift).toNat := ⟨_, rfl⟩
  have hκ'e : ∀ i, (mu.natW i : ℤ) + mu.detShift = mu.w i := by
    intro i
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hle : mu.w ⟨n - 1, by omega⟩ ≤ mu.w i :=
      mu.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn] at hle ⊢
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hcE : 0 < n → mu.detShift = lam.detShift + (d : ℤ) := by
    intro hn
    have := hge hn
    rw [hd, Int.toNat_of_nonneg (by omega)]
    omega
  have hκf : ∀ i, ((mu.natW i + d : ℕ) : ℤ) + lam.detShift = mu.w i := by
    intro i
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have h1 := hκ'e i
    have h2 := hcE hn
    push_cast
    omega
  have hκfA : Antitone (fun i => mu.natW i + d) := fun i j hij => Nat.add_le_add_right (natW_antiC mu hij) d

  obtain ⟨hUf, hTf⟩ := fixed_data (k := 1) f lam.detShift mu.w (fun i => mu.natW i + d) hκf
    (fun g h1 h2 => by
      have := hfix.1 g h1 h2
      rwa [sqAct_eq, embGL_coe, iotaC_det] at this)
    (fun t => by
      have := hfix.2 t
      rw [sqAct_eq, embGL_coe, iotaC_det] at this
      have hdg : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun a => (t a : ℂ) := rfl
      rw [hdg, Matrix.det_diagonal, Units.coe_prod] at this
      simpa only [Units.val_zpow_eq_zpow_val] using this)
  obtain ⟨hUe, hTe⟩ := fixed_data (k := 0) (extremal ℂ n mu) mu.detShift mu.w mu.natW hκ'e
    (fun g h1 h2 => by
      rw [iotaC_zero]
      have := (he n mu).1 g h1 h2
      rwa [sqAct_eq] at this)
    (fun t => by
      rw [iotaC_zero]
      have := (he n mu).2.1 t
      rw [sqAct_eq] at this
      have hdg : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun a => (t a : ℂ) := rfl
      rw [hdg, Matrix.det_diagonal, Units.coe_prod] at this
      simpa only [Units.val_zpow_eq_zpow_val] using this)

  have gf : ∀ g g' : GL (Fin n) ℂ, fockF (vfC n lam f g) (vfC n lam f g') =
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift)) *
        (fockF f f * hwAt (fun i => mu.natW i + d)
          ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))) := by
    intro g g'
    unfold vfC
    rw [sqAct_eq, sqAct_eq, embGL_coe, embGL_coe, iotaC_det, iotaC_det, fockF_smul_left, fockF_smul_right,
      gram_of _ hκfA hUf hTf]
    ring
  have ge : ∀ g g' : GL (Fin n) ℂ, fockF (veC n mu g) (veC n mu g') =
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift)) *
        (fockF (extremal ℂ n mu) (extremal ℂ n mu) * hwAt mu.natW
          ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))) := by
    intro g g'
    unfold veC
    have := gram_of (k := 0) (f := extremal ℂ n mu) mu.natW (natW_antiC mu) hUe hTe
      (g : Matrix (Fin n) (Fin n) ℂ) (g' : Matrix (Fin n) (Fin n) ℂ)
    rw [iotaC_zero, iotaC_zero] at this
    rw [sqAct_eq, sqAct_eq, fockF_smul_left, fockF_smul_right, this]
    ring
  have hee : fockF (extremal ℂ n mu) (extremal ℂ n mu) ≠ 0 := by
    intro h0
    have := (fockPos _ (extremal ℂ n mu) heN).1
    rw [h0] at this
    simp at this
  have hK : ∀ g g' : GL (Fin n) ℂ, fockF (vfC n lam f g) (vfC n lam f g') =
      (fockF f f / fockF (extremal ℂ n mu) (extremal ℂ n mu)) * fockF (veC n mu g) (veC n mu g') := by
    intro g g'
    rw [gf, ge, hwAt_shift, Matrix.det_mul, Matrix.det_conjTranspose]
    have ha0 : (g : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have hb0 : (g' : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have tw : (g : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ lam.detShift) *
        (star (g' : Matrix (Fin n) (Fin n) ℂ).det * (g : Matrix (Fin n) (Fin n) ℂ).det) ^ d =
        (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift * star ((g' : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [Matrix.det_isEmpty]
      · exact twist_id _ _ ha0 hb0 _ _ _ (hcE hn)
    set a := (g : Matrix (Fin n) (Fin n) ℂ).det
    set b := (g' : Matrix (Fin n) (Fin n) ℂ).det
    set H := hwAt mu.natW ((g' : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ))
    set ee := fockF (extremal ℂ n mu) (extremal ℂ n mu)
    calc a ^ lam.detShift * star (b ^ lam.detShift) * (fockF f f * ((star b * a) ^ d * H))
        = (a ^ lam.detShift * star (b ^ lam.detShift) * (star b * a) ^ d) * fockF f f * H := by ring
      _ = (a ^ mu.detShift * star (b ^ mu.detShift)) * fockF f f * H := by rw [tw]
      _ = (fockF f f / ee * ee) * (a ^ mu.detShift * star (b ^ mu.detShift)) * H := by
          rw [div_mul_cancel₀ _ hee]; ring
      _ = fockF f f / ee * (a ^ mu.detShift * star (b ^ mu.detShift) * (ee * H)) := by ring

  set Le := Finsupp.linearCombination ℂ (veC n mu) with hLe
  set Lf := Finsupp.linearCombination ℂ (vfC n lam f) with hLf
  have hker : LinearMap.ker Le ≤ LinearMap.ker Lf := by
    intro c hc
    rw [LinearMap.mem_ker, hLe, Finsupp.linearCombination_apply, Finsupp.sum] at hc
    rw [LinearMap.mem_ker, hLf, Finsupp.linearCombination_apply, Finsupp.sum]
    exact lc_zero_of_gram c.support c (veC n mu) (vfC n lam f) _ hK hc
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend
    (((LinearMap.ker Le).liftQ Lf hker).comp (Le.quotKerEquivRange.symm : LinearMap.range Le →ₗ[ℂ] _))
  have hφv : ∀ c, φ (Le c) = Lf c := by
    intro c
    have h1 := LinearMap.congr_fun hφ ⟨Le c, LinearMap.mem_range_self Le c⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at h1
    exact h1

  have hrange : LinearMap.range Le = nablaSq ℂ n mu := by
    rw [hLe, Finsupp.range_linearCombination]
    have hle : Submodule.span ℂ (Set.range (veC n mu)) ≤ nablaSq ℂ n mu :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact (he n mu).2.2 g _ heM)
    have hst : ∀ g : GL (Fin n) ℂ, ∀ x ∈ Submodule.span ℂ (Set.range (veC n mu)),
        sqAct ℂ n mu g x ∈ Submodule.span ℂ (Set.range (veC n mu)) := by
      intro g x hx
      have : Submodule.span ℂ (Set.range (veC n mu)) ≤
          (Submodule.span ℂ (Set.range (veC n mu))).comap (sqLC n mu g) := by
        rw [Submodule.span_le]
        rintro _ ⟨g', rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, sqLC_apply]
        exact Submodule.subset_span ⟨g * g', by simp only [veC, sqAct_mulC]⟩
      exact this hx
    rcases (h n mu).2.1 _ hle hst with h0 | h1
    · exfalso
      apply heN
      have : extremal ℂ n mu ∈ Submodule.span ℂ (Set.range (veC n mu)) :=
        Submodule.subset_span ⟨1, by simp only [veC, sqAct_oneC]⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h1
  have hfL : ∀ c, Lf c ∈ nablaSq ℂ (n + 1) lam := by
    intro c
    have : Lf c ∈ Submodule.span ℂ (Set.range (vfC n lam f)) := by
      rw [← Finsupp.range_linearCombination, ← hLf]
      exact LinearMap.mem_range_self _ c
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact (he (n + 1) lam).2.2 _ f hf) this
  have hLe_g : ∀ (g : GL (Fin n) ℂ) c, sqAct ℂ n mu g (Le c) = Le (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have hfun : (⇑(sqLC n mu g) ∘ veC n mu) = (veC n mu ∘ (g * ·)) := by
      funext g'
      simp only [Function.comp_apply, sqLC_apply, veC, sqAct_mulC]
    rw [hLe, Finsupp.linearCombination_mapDomain, ← sqLC_apply, Finsupp.apply_linearCombination, hfun]
  have hLf_g : ∀ (g : GL (Fin n) ℂ) c, sqAct ℂ (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g) (Lf c) =
      Lf (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    have hfun : (⇑(sqLC (n + 1) lam (PI.embGL ℂ n (n + 1) rfl g)) ∘ vfC n lam f) = (vfC n lam f ∘ (g * ·)) := by
      funext g'
      simp only [Function.comp_apply, sqLC_apply, vfC, map_mul, sqAct_mulC]
    rw [hLf, Finsupp.linearCombination_mapDomain, ← sqLC_apply, Finsupp.apply_linearCombination, hfun]
  refine ⟨φ, ⟨fun s hs => ?_, fun g s hs => ?_⟩, ?_⟩
  · rw [← hrange] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [hφv]
    exact hfL c
  · rw [← hrange] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [hLe_g, hφv, hφv, hLf_g]
  · have h1 : extremal ℂ n mu = Le (Finsupp.single 1 1) := by
      rw [hLe, Finsupp.linearCombination_single, one_smul]
      simp only [veC, sqAct_oneC]
    rw [h1, hφv, hLf, Finsupp.linearCombination_single, one_smul]
    simp only [vfC, map_one, sqAct_oneC]

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem realize_of (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) : Realize := by
  intro n N hN lam mu f hf hfix hne
  subst hN
  exact realize_C h he ha n lam mu f hf hfix hne

end PI.WGB
