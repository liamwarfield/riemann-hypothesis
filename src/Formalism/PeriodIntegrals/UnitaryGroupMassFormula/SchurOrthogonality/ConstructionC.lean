module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CiEvalMSmul
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CrRowActRowAct
noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cr_rowAct_X {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (w : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (X w : MvPolynomial (Fin N × Fin N) ℂ) = ∑ b : Fin N, C (g w.1 b) * X (b, w.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem cr_rowAct_C {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).commutes a

theorem cr_evalM_rowAct {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by
  induction s using MvPolynomial.induction_on
  next a =>
    rw [cr_rowAct_C]
    simp [evalM]
  next p q hp hq =>
    simp only [map_add (f := _), evalM] at hp hq ⊢
    rw [hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp, cr_rowAct_X]
    congr 1
    simp [Matrix.mul_apply]

theorem cr_rowAct_one {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) s = s := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [cr_rowAct_X]
    simp [Matrix.one_apply]
  rw [h]
  rfl

theorem cr_rowAct_rowAct {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h s) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) s := by
  have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, cr_rowAct_X, map_sum, cr_rowAct_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, cr_rowAct_C, cr_rowAct_X, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
  rw [← hc, AlgHom.comp_apply]

theorem cr_polyFun {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    ∀ L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ, ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ, L (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM g P := by
  intro L
  let Φ : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) ℂ) :=
    aeval fun v => ∑ b : Fin N, C (X (v.1, b) : MvPolynomial (Fin N × Fin N) ℂ) * X (b, v.2)
  have hmap : ∀ g : Matrix (Fin N) (Fin N) ℂ,
      MvPolynomial.map (MvPolynomial.eval fun v : Fin N × Fin N => g v.1 v.2) (Φ s) = Formalism.GradedWeylDivisibility.rowAct ℂ g s := by
    intro g
    induction s using MvPolynomial.induction_on
    next a =>
      rw [cr_rowAct_C]
      simp [Φ]
    next p q hp hq =>
      simp only [map_add (f := _), hp, hq]
    next p w hp =>
      simp only [map_mul, hp, cr_rowAct_X]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        MvPolynomial.eval_X]
  have hmono : ∀ (m : Fin N × Fin N →₀ ℕ) (a : ℂ), L (monomial m a) = a * L (monomial m 1) := by
    intro m a
    calc L (monomial m a) = L (a • monomial m (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
      _ = a * L (monomial m 1) := by rw [map_smul, smul_eq_mul]
  refine ⟨∑ m ∈ (Φ s).support, (Φ s).coeff m * C (L (monomial m 1)), fun g => ?_⟩
  rw [← hmap g]
  conv_lhs => rw [(Φ s).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.map_monomial, evalM, map_mul, MvPolynomial.eval_C]
  exact Finset.sum_congr rfl fun m _ => hmono m _

end PI.WSF
end
end

noncomputable section

namespace PI.WSF

open MvPolynomial MeasureTheory Matrix

private theorem entry_le_lemma {N : ℕ} {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ unitaryGroup (Fin N) ℂ)
    (i j : Fin N) : ‖x i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hx) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h3 : (∑ k, Complex.normSq (x i k) : ℝ) = 1 := by
    have h4 : ((∑ k, Complex.normSq (x i k) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h]
      exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (x i k)).symm
    exact_mod_cast h4
  have h5 : Complex.normSq (x i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at h5
  nlinarith [norm_nonneg (x i j)]

theorem ci_compact (N : ℕ) : IsCompact (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hset : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) = {x | x * star x = 1} := by
    ext x
    exact Matrix.mem_unitaryGroup_iff
  have hclosed : IsClosed (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    rw [hset]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have hbound : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
      mem_closedBall_zero_iff.mpr (entry_le_lemma hx i j)
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset
    hclosed hbound

theorem ci_cont {N : ℕ} (p : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p := by
  unfold evalM
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun v => (continuous_apply v.2).comp (continuous_apply v.1))

theorem ci_cont2 {N : ℕ} (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p * star (evalM x q) :=
  (ci_cont p).mul (ci_cont q).star

theorem ci_integrable {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    {f : Matrix (Fin N) (Fin N) ℂ → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨hprob, hae, -, -⟩ := hμ
  have h := hf.continuousOn.integrableOn_compact (μ := μ) (ci_compact N)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h
  exact h

theorem ci_evalM_add {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (p + q) = evalM x p + evalM x q := by
  simp [evalM]

theorem ci_evalM_smul {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (c • p) = c * evalM x p := by
  simp [evalM]

def Aform {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  ∫ x, evalM x p * star (evalM x q) ∂μ

def Alin {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (q : MvPolynomial (Fin N × Fin N) ℂ) : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := Aform μ p q
  map_add' p p' := by
    unfold Aform
    rw [← integral_add (ci_integrable hμ (ci_cont2 p q)) (ci_integrable hμ (ci_cont2 p' q))]
    congr 1
    funext x
    rw [ci_evalM_add]
    ring
  map_smul' c p := by
    unfold Aform
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [ci_evalM_smul]
    ring

theorem ci_Alin_apply {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) : Alin hμ q p = Aform μ p q := rfl

theorem ci_herm {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ q p = star (Aform μ p q) := by
  unfold Aform
  have h := integral_conj (μ := μ) (f := fun x => evalM x p * star (evalM x q))
  rw [show star (∫ x, evalM x p * star (evalM x q) ∂μ) =
    (starRingEnd ℂ) (∫ x, evalM x p * star (evalM x q) ∂μ) from rfl, ← h]
  congr 1
  funext x
  simp [mul_comm]

private theorem evalM_rowAct {N : ℕ} (u x : Matrix (Fin N) (Fin N) ℂ)
    (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ u p) = evalM (u * x) p := by
  induction p using MvPolynomial.induction_on
  next a =>
    simp [evalM, Formalism.GradedWeylDivisibility.rowAct]
  next p q hp hq =>
    rw [map_add (f := _), ci_evalM_add, ci_evalM_add, hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem ci_invariant {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ unitaryGroup (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (Formalism.GradedWeylDivisibility.rowAct ℂ u p) (Formalism.GradedWeylDivisibility.rowAct ℂ u q) = Aform μ p q := by
  obtain ⟨-, -, -, hL⟩ := hμ
  unfold Aform
  simp only [evalM_rowAct]
  exact hL u hu (fun x => evalM x p * star (evalM x q)) (ci_cont2 p q)

end PI.WSF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CfEqSumOfSubset
noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cf_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul, zero_mul]

theorem cf_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [cf_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    cf_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    cf_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem cf_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left]

theorem cf_F {N : ℕ} (lam : DomWeight N) :
    (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 ∧
      0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re := by
  have hne : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.fockPos _ _ hne
  exact ⟨h2, h1⟩

theorem cf_F_ne {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  intro h0
  have h1 := (cf_F lam).2
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

def Blin {N : ℕ} (lam : DomWeight N) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := normFock lam p q
  map_add' p p' := by
    simp only [normFock]
    rw [cf_add_left, add_div]
  map_smul' c p := by
    simp only [normFock, RingHom.id_apply, smul_eq_mul]
    rw [cf_smul_left, mul_div_assoc]

theorem cf_Blin_apply {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Blin lam q p = normFock lam p q := rfl

theorem cf_herm {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam q p = star (normFock lam p q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockHerm, star_div₀]
  congr 1
  have h := (cf_F lam).1
  apply Complex.ext
  · simp
  · simp [h]

theorem normFock_self_ne_zero {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) (hp : p ≠ 0) :
    normFock lam p p ≠ 0 := by
  unfold normFock
  refine div_ne_zero ?_ (cf_F_ne lam)
  intro h0
  have h1 := (Formalism.GradedWeylDivisibility.fockPos _ p hp).1
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

theorem cf_adj {N : ℕ} (lam : DomWeight N) (g : Matrix (Fin N) (Fin N) ℂ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (Formalism.GradedWeylDivisibility.rowAct ℂ g p) q = normFock lam p (Formalism.GradedWeylDivisibility.rowAct ℂ g.conjTranspose q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockRowAdj]

theorem cf_ee {N : ℕ} (lam : DomWeight N) : normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  exact div_self (cf_F_ne lam)

end PI.WSF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CzDiagUnitary
noncomputable section

namespace PI.WSF

open MvPolynomial Matrix
open scoped ComplexOrder

private theorem setOf_norm_eq_one_infinite : ({z : ℂ | ‖z‖ = 1} : Set ℂ).Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite := Set.Ioc_infinite (by linarith [Real.pi_pos])
  refine Set.infinite_of_injOn_mapsTo
    (f := fun θ : ℝ => Complex.cos θ + Complex.sin θ * Complex.I) ?_ ?_ hI
  · intro a ha b hb hab
    have h1 := congrArg Complex.arg hab
    simp only at h1
    rwa [Complex.arg_cos_add_sin_mul_I ha, Complex.arg_cos_add_sin_mul_I hb] at h1
  · intro θ _
    exact Complex.norm_cos_add_sin_mul_I θ

theorem cz_torus_zero {ι : Type*} [Fintype ι] (Q : MvPolynomial ι ℂ)
    (h : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) → eval z Q = 0) : Q = 0 := by
  rw [MvPolynomial.funext_set_iff (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => setOf_norm_eq_one_infinite)]
  intro x hx
  rw [map_zero]
  exact h x (fun i => hx i (Set.mem_univ i))

def czFam {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N) ℂ :=
  bind₁ (fun w : Fin N × Fin N => ∑ c : Fin N, C (u w.1 c * v c w.2) * X c) P

theorem czFam_eval {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ)
    (z : Fin N → ℂ) : eval z (czFam u v P) = evalM (u * diagonal z * v) P := by
  have h1 : eval z (czFam u v P) =
      eval (fun w : Fin N × Fin N => eval z (∑ c : Fin N, C (u w.1 c * v c w.2) * X c)) P := by
    unfold czFam
    exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  rw [h1]
  unfold evalM
  refine congrArg (fun x => eval x P) ?_
  funext w
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem cz_diag_unitary {N : ℕ} (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    diagonal z ∈ unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 := RCLike.mul_conj (z i)
  rw [hz i] at h1
  simpa using h1

theorem cz_svd {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det) :
    ∃ u ∈ unitaryGroup (Fin N) ℂ, ∃ v ∈ unitaryGroup (Fin N) ℂ, ∃ z : Fin N → ℂ,
      g = u * diagonal z * v := by
  classical
  have hA : (gᴴ * g).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self g
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg g
  set W : Matrix (Fin N) (Fin N) ℂ := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hW
  have hWu : W ∈ unitaryGroup (Fin N) ℂ := hA.eigenvectorUnitary.2
  have hWW : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hWu
  have hWW' : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hWu
  have hD : Wᴴ * (gᴴ * g) * W = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h1 := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h1
    rw [← Matrix.star_eq_conjTranspose]
    exact h1
  have hdet : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
    have h1 : Wᴴ.det * W.det = 1 := by rw [← Matrix.det_mul, hWW, Matrix.det_one]
    have h2 : gᴴ.det ≠ 0 := by
      rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hg.ne_zero
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1)
      (mul_ne_zero h2 hg.ne_zero)) (right_ne_zero_of_mul_eq_one h1)
  have hpos : ∀ i, 0 < hA.eigenvalues i := by
    intro i
    rw [Matrix.det_diagonal] at hdet
    have h1 := Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
    have h2 : hA.eigenvalues i ≠ 0 := by
      intro h3
      apply h1
      simp [h3]
    exact lt_of_le_of_ne (hnn i) (Ne.symm h2)
  set s : Fin N → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hs
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i
    simp only [hs, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hpos i)).ne'
  have hs2 : ∀ i, star (s i) * s i = RCLike.ofReal (hA.eigenvalues i) := by
    intro i
    change star (s i) * s i = ((hA.eigenvalues i : ℝ) : ℂ)
    simp only [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hnn i)]
  refine ⟨g * W * diagonal (fun i => (s i)⁻¹), ?_, Wᴴ, ?_, s, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    have key : diagonal (star fun i => (s i)⁻¹) * (Wᴴ * gᴴ) * (g * W * diagonal fun i => (s i)⁻¹)
        = diagonal (star fun i => (s i)⁻¹) * (Wᴴ * (gᴴ * g) * W) * diagonal fun i => (s i)⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [key, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hs2 i
    have h2 : star (s i) ≠ 0 := star_ne_zero.mpr (hs0 i)
    simp only [Pi.star_apply, Function.comp_apply, star_inv₀, ← h1]
    field_simp
    exact div_self (hs0 i)
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hWW
  · rw [Matrix.mul_assoc (g * W), Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) := by
      funext i; exact inv_mul_cancel₀ (hs0 i)
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_assoc, hWW', Matrix.mul_one]

theorem cz_zariski {N : ℕ} (P : MvPolynomial (Fin N × Fin N) ℂ)
    (h : ∀ u ∈ unitaryGroup (Fin N) ℂ, evalM u P = 0) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : IsUnit g.det) : evalM g P = 0 := by
  obtain ⟨u, hu, v, hv, z, rfl⟩ := cz_svd g hg
  have hQ : czFam u v P = 0 := by
    apply cz_torus_zero
    intro w hw
    rw [czFam_eval]
    exact h _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hu (cz_diag_unitary w hw)) hv)
  have h1 := czFam_eval u v P z
  rw [hQ, map_zero] at h1
  exact h1.symm

end PI.WSF
end
end

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Matrix

private lemma normFock_add_left {N : ℕ} (lam : DomWeight N) (p p' q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (p + p') q = normFock lam p q + normFock lam p' q := by
  simpa [cf_Blin_apply] using (Blin lam q).map_add p p'

private lemma normFock_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • p) q = c * normFock lam p q := by
  have := (Blin lam q).map_smul c p
  rwa [cf_Blin_apply, cf_Blin_apply, smul_eq_mul] at this

private lemma aform_sum_smul_left {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ) {ι : Type*}
    (t : Finset ι) (c : ι → ℂ) (p : ι → MvPolynomial (Fin N × Fin N) ℂ) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (∑ i ∈ t, c i • p i) q = ∑ i ∈ t, c i * Aform μ (p i) q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← ci_Alin_apply hμ, map_sum, map_smul, smul_eq_mul]

private lemma exists_nonneg_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.REAL.fockF f f = (r : ℂ) := by
  refine ⟨∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ),
    Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _), ?_⟩
  unfold Formalism.REAL.fockF
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

private lemma normFock_self_re_nonneg_and_real {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam p p).re ∧ normFock lam p p = ((normFock lam p p).re : ℂ) := by
  obtain ⟨a, ha, hpa⟩ := exists_nonneg_fockF_self p
  obtain ⟨b, hb, heb⟩ := exists_nonneg_fockF_self (extremal ℂ N lam)
  have h : normFock lam p p = ((a / b : ℝ) : ℂ) := by
    rw [normFock, hpa, heb, Complex.ofReal_div]
  rw [h, Complex.ofReal_re]
  exact ⟨div_nonneg ha hb, rfl⟩

theorem schurOrth_of (h : PI.HwIrred) (hA : EvalOne) : SchurOrth := by
  intro N lam μ hμ s hs
  set V : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := nablaSq ℂ N lam with hV
  have hstab : ∀ (g : Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ), f ∈ V →
      Formalism.GradedWeylDivisibility.rowAct ℂ g f ∈ V :=
    fun g f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW g f hf
  have anti : Antitone lam.natW := fun a b hab => by
    have := lam.anti hab
    exact Int.toNat_le_toNat (by omega)
  have he : extremal ℂ N lam ∈ V := Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW anti
  have he0 : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  haveI : FiniteDimensional ℂ V := by
    obtain ⟨bb, ⟨-, hspan, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ N N lam.natW
    haveI : Finite (Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N lam.natW).to_subtype
    have : V = Submodule.span ℂ (Set.range bb) := hspan.symm
    rw [this]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range bb)
  haveI : Nontrivial V := ⟨⟨⟨_, he⟩, 0, fun h0 => he0 (congrArg Subtype.val h0)⟩⟩
  letI core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) x
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (normFock lam (x : MvPolynomial (Fin N × Fin N) ℂ) y) = normFock lam y x
        rw [cf_herm lam (x : MvPolynomial (Fin N × Fin N) ℂ) y]
        rfl
      re_inner_nonneg := fun x => (normFock_self_re_nonneg_and_real lam x).1
      add_left := fun x y z => by
        show normFock lam (z : MvPolynomial (Fin N × Fin N) ℂ) ((x + y : V) : MvPolynomial (Fin N × Fin N) ℂ) =
          normFock lam z x + normFock lam z y
        rw [Submodule.coe_add, cf_herm lam ((x : MvPolynomial (Fin N × Fin N) ℂ) + y) z, normFock_add_left, star_add,
          ← cf_herm, ← cf_herm]
      smul_left := fun x y r => by
        show normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) ((r • x : V) : MvPolynomial (Fin N × Fin N) ℂ) =
          (starRingEnd ℂ) r * normFock lam y x
        rw [Submodule.coe_smul, cf_herm lam (r • (x : MvPolynomial (Fin N × Fin N) ℂ)) y, normFock_smul_left, star_mul',
          ← cf_herm]
        rfl
      definite := fun x hx => by
        by_contra hne
        exact normFock_self_ne_zero lam (x : MvPolynomial (Fin N × Fin N) ℂ) (fun h0 => hne (Subtype.ext h0)) hx }
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hin : ∀ x y : V, @inner ℂ V _ x y = normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  let rv : Matrix (Fin N) (Fin N) ℂ → V → V := fun g x => ⟨Formalism.GradedWeylDivisibility.rowAct ℂ g x, hstab g x x.2⟩
  have hrv : ∀ g (x : V), (rv g x : MvPolynomial (Fin N × Fin N) ℂ) = Formalism.GradedWeylDivisibility.rowAct ℂ g x := fun _ _ => rfl
  have hunit : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.GradedWeylDivisibility.rowAct ℂ u (Formalism.GradedWeylDivisibility.rowAct ℂ u.conjTranspose f) = f := by
    intro u hu f
    rw [cr_rowAct_rowAct, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hu, cr_rowAct_one]

  let T : V →ₗ[ℂ] V := ∑ i, ((Alin hμ (b i : MvPolynomial (Fin N × Fin N) ℂ)).comp V.subtype).smulRight (b i)
  have hTapp : ∀ x : V, T x = ∑ i, Aform μ (x : MvPolynomial (Fin N × Fin N) ℂ) (b i) • b i := by
    intro x
    simp only [T]
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, ci_Alin_apply]
  have hT : ∀ x w : V, @inner ℂ V _ (T x) w = Aform μ (w : MvPolynomial (Fin N × Fin N) ℂ) x := by
    intro x w
    have hw : (w : MvPolynomial (Fin N × Fin N) ℂ) =
        ∑ i, @inner ℂ V _ (b i) w • (b i : MvPolynomial (Fin N × Fin N) ℂ) := by
      conv_lhs => rw [← b.sum_repr' w]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hTapp, sum_inner, hw, aform_sum_smul_left hμ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, ci_herm μ (x : MvPolynomial (Fin N × Fin N) ℂ) (b i), mul_comm]
    rfl
  have hcomm : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ x : V, T (rv u x) = rv u (T x) := by
    intro u hu x
    refine ext_inner_right ℂ fun w => ?_
    have e1 : @inner ℂ V _ (rv u (T x)) w = @inner ℂ V _ (T x) (rv u.conjTranspose w) := by
      rw [hin, hin, hrv, hrv, cf_herm lam ((Formalism.GradedWeylDivisibility.rowAct ℂ u) (T x : MvPolynomial (Fin N × Fin N) ℂ)) w, cf_adj,
        ← cf_herm]
    rw [hT, e1, hT, hrv, ← ci_invariant hμ u hu (Formalism.GradedWeylDivisibility.rowAct ℂ u.conjTranspose w) x, hunit u hu]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v0, hv0⟩ := hc.exists_hasEigenvector
  have hkey : ∀ y : V, T y = c • y → ∀ g : Matrix (Fin N) (Fin N) ℂ, IsUnit g.det → T (rv g y) = c • rv g y := by
    intro y hy g hg
    set z : V := T (rv g y) - c • rv g y with hz
    let ℓ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ z).comp (T - c • LinearMap.id)
    obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
    have hLv : ∀ p : V, L p = @inner ℂ V _ z (T p) - c * @inner ℂ V _ z p := fun p => by
      have h2 := LinearMap.congr_fun hL p
      simp [ℓ] at h2
      rw [h2, inner_sub_right, inner_smul_right]
    obtain ⟨P, hP⟩ := cr_polyFun (y : MvPolynomial (Fin N × Fin N) ℂ) L
    have hu0 : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, evalM u P = 0 := by
      intro u hu
      rw [← hP u, ← hrv u y, hLv, hcomm u hu, hy]
      have : rv u (c • y) = c • rv u y := Subtype.ext (by simp [hrv, map_smul])
      rw [this, inner_smul_right, sub_self]
    have h0 := cz_zariski P hu0 g hg
    rw [← hP g, ← hrv g y, hLv] at h0
    have hzz : @inner ℂ V _ z z = 0 := by
      nth_rewrite 2 [hz]
      rw [inner_sub_right, inner_smul_right]
      exact h0
    rw [← sub_eq_zero]
    exact inner_self_eq_zero.mp hzz
  let K := LinearMap.ker (T - c • LinearMap.id)
  have hK : ∀ y : V, y ∈ K ↔ T y = c • y := fun y => by
    simp [K, sub_eq_zero]
  let W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := K.map V.subtype
  have hWle : W ≤ nablaSq ℂ N lam := Submodule.map_subtype_le V K
  have hWinv : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ W, sqAct ℂ N lam g f ∈ W := by
    intro g f hf
    obtain ⟨y, hy, rfl⟩ := hf
    have hg : IsUnit ((g : Matrix (Fin N) (Fin N) ℂ).transpose).det := by
      rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g
    refine W.smul_mem _ ⟨rv (g : Matrix (Fin N) (Fin N) ℂ).transpose y, (hK _).mpr
      (hkey y ((hK y).mp hy) _ hg), rfl⟩
  have hWne : W ≠ ⊥ := by
    intro h0
    have : (v0 : MvPolynomial (Fin N × Fin N) ℂ) ∈ W := ⟨v0, (hK v0).mpr hv0.apply_eq_smul, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact hv0.2 (Subtype.ext this)
  have hall : ∀ y : V, T y = c • y := by
    intro y
    rcases (h N lam).2.1 W hWle hWinv with h0 | h0
    · exact absurd h0 hWne
    · have : (y : MvPolynomial (Fin N × Fin N) ℂ) ∈ W := by rw [h0]; exact y.2
      obtain ⟨y', hy', hyy⟩ := this
      rw [← (Subtype.ext hyy : y' = y)]
      exact (hK y').mp hy'
  have hAB : ∀ x w : V, Aform μ (w : MvPolynomial (Fin N × Fin N) ℂ) x =
      (starRingEnd ℂ) c * normFock lam (w : MvPolynomial (Fin N × Fin N) ℂ) x := by
    intro x w
    rw [← hT, hall, inner_smul_left, hin]

  have hsum1 : ∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ,
      ∑ i, evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ) * star (evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    intro x hx
    let y : V := rv x.conjTranspose ⟨_, he⟩
    have hev : ∀ i, evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ) = @inner ℂ V _ y (b i) := by
      intro i
      have h1 := cr_evalM_rowAct x 1 (b i : MvPolynomial (Fin N × Fin N) ℂ)
      rw [mul_one] at h1
      rw [← h1, hA N lam _ (hstab x _ (b i).2), cf_adj, hin]
    simp only [hev]
    have : ∀ i, star (@inner ℂ V _ y (b i)) = @inner ℂ V _ (b i) y := fun i => inner_conj_symm _ _
    simp only [this]
    rw [b.sum_inner_mul_inner y y, hin, hrv, cf_adj, Matrix.conjTranspose_conjTranspose, hunit x hx]
    exact cf_ee lam
  have htrace : ∑ i, Aform μ (b i : MvPolynomial (Fin N × Fin N) ℂ) (b i) = 1 := by
    simp only [Aform]
    rw [← MeasureTheory.integral_finsetSum _ fun i _ => ci_integrable hμ (ci_cont2 _ _)]
    rw [integral_congr_ae (g := fun _ => (1 : ℂ)) ?_]
    · haveI := hμ.1
      simp
    · filter_upwards [hμ.2.1] with x hx
      exact hsum1 x hx
  have hcd : (starRingEnd ℂ) c * (Module.finrank ℂ V : ℂ) = 1 := by
    have hdiag : ∀ i, Aform μ (b i : MvPolynomial (Fin N × Fin N) ℂ) (b i) = (starRingEnd ℂ) c := by
      intro i
      rw [hAB, ← hin]
      have : @inner ℂ V _ (b i) (b i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
      rw [this, mul_one]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htrace
    rw [mul_comm]; exact htrace
  have hss : normFock lam s s = (Module.finrank ℂ V : ℂ) * Aform μ s s := by
    rw [show s = ((⟨s, hs⟩ : V) : MvPolynomial (Fin N × Fin N) ℂ) from rfl, hAB, ← mul_assoc,
      mul_comm (Module.finrank ℂ V : ℂ), hcd, one_mul]
  have hint : Aform μ s s = ((∫ x, ‖evalM x s‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [Aform, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdim : Module.finrank ℂ (delSq ℂ N lam) = Module.finrank ℂ V := by
    rw [hV, (h N lam).1]
  rw [hss, hint, hdim, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]

end PI.WSF
