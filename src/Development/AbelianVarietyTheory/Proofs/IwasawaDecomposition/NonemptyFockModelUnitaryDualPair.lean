module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCover
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CoherentDense

open MvPolynomial

theorem eq_zero_of_hasSum_pow (a : ℕ → ℂ) (h : ∀ t : ℂ, HasSum (fun n => t ^ n * a n) 0) : a = 0 := by
  have h1 : HasFPowerSeriesAt (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun t => by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using h t
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h1.eq_zero

theorem eq_zero_of_hasSum_monomial {σ : Type} [Fintype σ] (c : (σ →₀ ℕ) → ℂ)
    (h : ∀ x : σ → ℂ, HasSum (fun α : σ →₀ ℕ => c α * α.prod fun l k => x l ^ k) 0) : c = 0 := by
  classical
  let S : ℕ → Finset (σ →₀ ℕ) := fun n => (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := fun n α => by simp [S]
  have key : ∀ n, (∑ α ∈ S n, monomial α (c α) : MvPolynomial σ ℂ) = 0 := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    have h1 : (fun m => eval x (∑ α ∈ S m, monomial α (c α) : MvPolynomial σ ℂ)) = 0 := by
      refine eq_zero_of_hasSum_pow _ fun t => ?_
      have h2 := (h (t • x)).tsum_fiberwise (fun α => α.degree)
      refine h2.congr_fun fun m => ?_
      have e : ((fun α : σ →₀ ℕ => α.degree) ⁻¹' {m}) = (S m : Set (σ →₀ ℕ)) := by
        ext α; simp [hS]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, Finset.tsum_subtype' (S m) (fun α : σ →₀ ℕ => c α * α.prod fun l k => (t • x) l ^ k), map_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [eval_monomial, ← (hS m α).1 hα, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      ring
    simpa using congrFun h1 n
  funext α
  have h3 := congrArg (AddMonoidAlgebra.coeff · α) (key α.degree)
  rw [coeff_sum, Finset.sum_eq_single α (fun β _ hβ => by simp [coeff_monomial, hβ])
    (fun hα => absurd ((hS _ α).2 rfl) hα)] at h3
  simpa using h3

theorem factorial_mul_coeff_expPS {σ : Type} [Fintype σ] (x : σ → ℂ) (α : σ →₀ ℕ) :
    α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (expPS (∑ l, x l • X l)) =
      α.prod fun l k => x l ^ k := by
  classical
  have hdeg : (α.sum fun _ e => e) = α.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [MvPowerSeries.coeff_apply, expPS, Finset.sum_eq_single α.degree]
  · rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : (α.prod fun _ k => k.factorial) * α.multinomial = α.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : α.prod (fun _ k => (k.factorial : ℂ)) * (α.multinomial : ℂ) = (α.degree.factorial : ℂ) := by
      rw [← hs]; simp [Finsupp.prod]
    have h0 : (α.degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
  · intro k _ hk
    rw [coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

theorem eq_zero_of_inner_monomial {σ : Type} [DecidableEq σ] (F : Fock σ) (u : F.H)
    (h : ∀ α, inner ℂ u (F.ι (monomial α 1)) = 0) : u = 0 := by
  refine F.dense.eq_zero_of_inner_left ℂ ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), inner_add_right, hf, hg, add_zero]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_right, h, mul_zero]

theorem hasSum_inner {σ : Type} [DecidableEq σ] (F : Fock σ) (u v : F.H) :
    HasSum (fun α : σ →₀ ℕ => inner ℂ u (F.ι (monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ)) *
      inner ℂ (F.ι (monomial α 1)) v) (inner ℂ u v) := by
  let m : (σ →₀ ℕ) → ℝ := fun α => α.prod fun _ k => (k.factorial : ℝ)
  have hm : ∀ α, 0 < m α := fun α => Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hm' : ∀ α : σ →₀ ℕ, α.prod (fun _ k => (k.factorial : ℂ)) = (m α : ℂ) := fun α => by
    simp [m, Finsupp.prod]
  let r : (σ →₀ ℕ) → ℂ := fun α => (((√(m α))⁻¹ : ℝ) : ℂ)
  have hr : ∀ α, (starRingEnd ℂ) (r α) = r α := fun α => Complex.conj_ofReal _
  have hr2 : ∀ α, r α * r α = (m α : ℂ)⁻¹ := fun α => by
    simp only [r]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hm α).le, Complex.ofReal_inv]
  have hm0 : ∀ α, (m α : ℂ) ≠ 0 := fun α => by exact_mod_cast (hm α).ne'
  have hr0 : ∀ α, r α ≠ 0 := fun α h => inv_ne_zero (hm0 α) (by rw [← hr2, h, mul_zero])
  let b : (σ →₀ ℕ) → F.H := fun α => r α • F.ι (monomial α 1)
  have hb : Orthonormal ℂ b := by
    rw [orthonormal_iff_ite]
    intro α β
    simp only [b, inner_smul_left, inner_smul_right, F.fockIP, hr]
    split_ifs with h
    · subst h
      rw [← mul_assoc, hr2, hm', inv_mul_cancel₀ (hm0 α)]
    · simp
  have hsp : (Submodule.span ℂ (Set.range b))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine eq_zero_of_inner_monomial F w fun α => ?_
    have := Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self α)) hw
    simpa [b, inner_smul_right, hr0] using this
  have h := (HilbertBasis.mkOfOrthogonalEqBot hb hsp).hasSum_inner_mul_inner u v
  refine h.congr_fun fun α => ?_
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [b, inner_smul_left, inner_smul_right, hr, hm', div_eq_mul_inv, ← hr2]
  ring

end GlobalTheory.CoherentDense


open GlobalTheory.CoherentDense in
theorem GlobalTheory.dense_span_coherent : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  intro P Q F e he
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hg : ∀ x : Ix P Q → ℂ, gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x = ∑ l, x l • MvPolynomial.X l := fun x => by
    simp [gaussPoly, MvPolynomial.smul_eq_C_mul]
  have h := eq_zero_of_hasSum_monomial
    (fun α => inner ℂ u (F.ι (MvPolynomial.monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ))) fun x => by
      have h1 := hasSum_inner F u (e x)
      rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self x)) hu] at h1
      simpa only [he x _, hg, factorial_mul_coeff_expPS] using h1
  refine eq_zero_of_inner_monomial F u fun α => ?_
  have h2 := congrFun h α
  have h0 : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simpa [h0] using h2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_span_coherent_vectors_fock : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  first | exact @GlobalTheory.dense_span_coherent | exact GlobalTheory.dense_span_coherent | (intros; apply GlobalTheory.dense_span_coherent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomial
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

theorem act_sum_blocks (Z : Mat P Q) (A E : Matrix (Fin P) (Fin Q) ℂ) (x d : Ix P Q → ℂ) (t : ℂ) :
    (∑ i, ∑ k, Z (.inl k) (.inl i) * (x (.inl i) * d (.inl k) + ∑ j, A i j * E k j + if i = k then t / 2 else 0) -
      ∑ i, ∑ j, Z (.inr j) (.inl i) * (x (.inl i) * (x (.inr j) * t + ∑ m, A m j * d (.inl m)) +
        (∑ k, A i k * (x (.inr j) * d (.inr k) + ∑ m, A m j * E m k) + A i j * t))) +
    (∑ j, ∑ i, Z (.inl i) (.inr j) * E i j -
      ∑ j, ∑ k, Z (.inr k) (.inr j) * (x (.inr k) * d (.inr j) + ∑ i, A i k * E i j + if j = k then t / 2 else 0)) =
    (Z.trace / 2 + dS Z A x) * t + (∑ i, ∑ j, dA Z A i j * E i j + ∑ l, dX Z A x l * d l) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    have h11 : (0 : Mat P Q).toBlocks₁₁ = 0 := rfl
    have h12 : (0 : Mat P Q).toBlocks₁₂ = 0 := rfl
    have h21 : (0 : Mat P Q).toBlocks₂₁ = 0 := rfl
    have h22 : (0 : Mat P Q).toBlocks₂₂ = 0 := rfl
    simp [dS, dA, dX, h11, h12, h21, h22]
  | h_add Z W hZ hW =>
    have h11 : (Z + W).toBlocks₁₁ = Z.toBlocks₁₁ + W.toBlocks₁₁ := rfl
    have h12 : (Z + W).toBlocks₁₂ = Z.toBlocks₁₂ + W.toBlocks₁₂ := rfl
    have h21 : (Z + W).toBlocks₂₁ = Z.toBlocks₂₁ + W.toBlocks₂₁ := rfl
    have h22 : (Z + W).toBlocks₂₂ = Z.toBlocks₂₂ + W.toBlocks₂₂ := rfl
    have hS : dS (Z + W) A x = dS Z A x + dS W A x := by
      simp only [dS, h21, h22, Matrix.add_mul, Matrix.trace_add, Matrix.add_mulVec, dotProduct_add]; ring
    have hA : dA (Z + W) A = dA Z A + dA W A := by
      simp only [dA, h11, h12, h21, h22, Matrix.add_mul, Matrix.mul_add]; abel
    have hX : dX (Z + W) A x = dX Z A x + dX W A x := by
      simp only [dX, h11, h21, h22, Matrix.add_mul, Matrix.mul_add, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.vecMul_add]
      ext (i | j) <;> simp <;> ring
    simp only [hS, hA, hX, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, Matrix.trace_add]
    simp only [add_mul] at hZ hW
    linear_combination hZ + hW
  | h_std_basis a b c =>
    rcases a with a | a <;> rcases b with b | b <;>
    simp [dS, dA, dX, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Matrix.mulVec, Matrix.vecMul, dotProduct, ite_and,
      Fintype.sum_sum_type]
    · simp only [mul_add, Finset.mul_sum, mul_assoc]
      split_ifs <;> ring
    · rw [Finset.sum_comm (f := fun i k => A i a * (c * A b k) * E i k)]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, mul_left_comm]
      ring
    · simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]
      split_ifs <;> ring


open MvPolynomial GlobalTheory.Oscillator in
theorem inner_omAct0_adjZ : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  intro P Q F A x v h1 h2 Z f
  have hh : ∀ (p : Prop) [Decidable p], inner ℂ (F.ι (if p then (1 / 2 : ℂ) • f else 0)) v =
      if p then inner ℂ (F.ι f) v / 2 else 0 := by
    intro p _
    split_ifs
    · rw [map_smul, inner_smul_left]; simp [map_ofNat]; ring
    · simp
  have hd : ∀ k j : Fin Q, inner ℂ (F.ι (pderiv (Sum.inr k) (X (Sum.inr j) * f))) v =
      x (.inr j) * inner ℂ (F.ι (pderiv (.inr k) f)) v +
        ∑ m, A m j * inner ℂ (F.ι (pderiv (.inl m) (pderiv (.inr k) f))) v +
        if k = j then inner ℂ (F.ι f) v else 0 := by
    intro k j
    rw [← h2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), inner_add_left, pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← act_sum_blocks Z A (fun i j => inner ℂ (F.ι (pderiv (Sum.inl i) (pderiv (Sum.inr j) f))) v) x
    (fun l => inner ℂ (F.ι (pderiv l f)) v) (inner ℂ (F.ι f) v), omAct0_eq, oscAct_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_smul_left,
    adjZ_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, LinearMap.add_apply, map_add, inner_add_left]
  simp only [unitOp_inl_inl, unitOp_inl_inr, unitOp_inr_inl, unitOp_inr_inr, map_add (f := _), map_sub, map_neg,
    inner_add_left, inner_sub_left, inner_neg_left, hh, h1, h2, hd, sgn, map_mul, Complex.conj_conj,
    Int.cast_one, Int.cast_neg, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hc : ∀ (j : Fin Q) (i : Fin P), pderiv (Sum.inr j) (pderiv (Sum.inl i) f) =
      pderiv (Sum.inl i) (pderiv (Sum.inr j) f) := fun j i => pderiv_pderiv_comm _ _ _
  rw [add_add_add_comm]
  simp only [hc, mul_add (A _ _), Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 2 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end GlobalTheory.OscGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  first | exact @GlobalTheory.OscGauss.inner_omAct0_adjZ | exact GlobalTheory.OscGauss.inner_omAct0_adjZ | (intros; apply GlobalTheory.OscGauss.inner_omAct0_adjZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRight
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem continuous_matrix_inv_of_isUnit_det {T n : Type} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {M : T → Matrix n n ℂ} (hM : Continuous M) (h : ∀ t, IsUnit (M t).det) : Continuous fun t => (M t)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun t => (h t).ne_zero).smul hM.matrix_adjugate

theorem continuous_ker_right (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ)
    (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ) (hY : Continuous Y')
    (hv : Continuous v') (hφ : Continuous φ') (h : ∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) :
    Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  have hM : Continuous fun t => Yᴴ * Jm P Q * Y' t := continuous_const.matrix_mul hY
  have hI := continuous_matrix_inv_of_isUnit_det hM h
  unfold ker
  refine (hM.neg.matrix_det.inv₀ fun t => ?_).mul (Complex.continuous_exp.comp (Continuous.sub
    (continuous_const.dotProduct hv) ((continuous_const.add hφ).dotProduct
      ((((hY.matrix_mul hI).matrix_mul continuous_const).matrix_mul continuous_const).matrix_mulVec
        (continuous_const.add hv)))))
  rw [Pi.neg_apply, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h t).ne_zero

end GlobalTheory.OscGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oscillatorGaussianKernel_right : ∀ (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ), Continuous Y' → Continuous v' → Continuous φ' → (∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) → Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  first | exact @GlobalTheory.OscGauss.continuous_ker_right | exact GlobalTheory.OscGauss.continuous_ker_right | (intros; apply GlobalTheory.OscGauss.continuous_ker_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVector
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix MvPolynomial Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.FockGauss

section Mat


open scoped MatrixOrder in
theorem re_sum_inner_nonneg {n H : Type} [Fintype n] [DecidableEq n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (u : n → H) :
    0 ≤ (∑ k, ∑ l, M k l * inner ℂ (u k) (u l)).re := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have : ∑ k, ∑ l, (star B * B) k l * inner ℂ (u k) (u l) =
      ∑ m, inner ℂ (∑ k, B m k • u k) (∑ l, B m l • u l) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply, Finset.sum_mul,
      Matrix.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (γ := n) (s := Finset.univ) (t := Finset.univ)
      (f := fun x m => star (B m x) * B m _ * inner ℂ (u x) (u _))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]; ring
  rw [this, Complex.re_sum]
  exact Finset.sum_nonneg fun m _ => inner_self_nonneg (𝕜 := ℂ)

theorem re_sum_inner_le {n H : Type} [Fintype n] [DecidableEq n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {M : Matrix n n ℂ} {r : ℝ} (hM : ((r : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef) (u : n → H) :
    (∑ k, ∑ l, M k l * inner ℂ (u k) (u l)).re ≤ r * ∑ k, ‖u k‖ ^ 2 := by
  have h := re_sum_inner_nonneg hM u
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.sub_re,
    sub_nonneg] at h
  refine h.trans_eq ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl


open scoped MatrixOrder in
theorem exists_bound {P Q : ℕ} {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef ∧
      ((r : ℂ) • (1 : Matrix (Fin P) (Fin P) ℂ) - A * Aᴴ).PosSemidef := by
  obtain ⟨δ, hδ, h1⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 - Aᴴ * A - (δ : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef := by
    rcases Nat.eq_zero_or_pos Q with rfl | hN
    · exact ⟨1, one_pos, by rw [Subsingleton.elim (_ - _) 0]; exact PosSemidef.zero⟩
    haveI : Nonempty (Fin Q) := ⟨⟨0, hN⟩⟩
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin Q) (Fin Q) ℂ)
      (1 - Aᴴ * A) h.isStrictlyPositive.isSelfAdjoint).2 fun x hx => h.isStrictlyPositive.spectrum_pos hx
    refine ⟨r, hr, ?_⟩
    have := Matrix.le_iff.mp hle
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
  set r : ℝ := max (1 - δ) (1 / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr0' : (0 : ℂ) < r := by exact_mod_cast hr0
  have h2 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef := by
    have h3 : (((r - (1 - δ) : ℝ) : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosSemidef :=
      PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 (le_max_left _ _))
    convert h1.add h3 using 1
    push_cast
    module
  refine ⟨r, hr0, max_lt (by linarith) (by norm_num), h2, ?_⟩
  have hD : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)).PosDef := PosDef.one.smul hr0'
  letI := hD.isUnit.invertible
  letI : Invertible (1 : Matrix (Fin P) (Fin P) ℂ) := invertibleOne
  have h4 := (PosDef.fromBlocks₁₁ A ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)) PosDef.one).2 (by simpa using h2)
  have h5 := ((PosDef.fromBlocks₂₂ 1 A hD).1 h4).smul hr0'.le
  have h6 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ))⁻¹ = (r : ℂ)⁻¹ • 1 :=
    Matrix.inv_eq_right_inv (by rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hr0'.ne', one_smul])
  rwa [h6, smul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hr0'.ne',
    one_smul] at h5

end Mat

section General

variable {σ : Type} [DecidableEq σ] (F : Fock σ)

theorem isFockIP : GlobalTheory.FockAlg.IsFockIP F.ι := fun α β => by convert F.fockIP α β

def DegLt (k : ℕ) (f : MvPolynomial σ ℂ) : Prop := ∀ α : σ →₀ ℕ, k ≤ α.degree → AddMonoidAlgebra.coeff f α = 0

omit [DecidableEq σ] in
theorem DegLt.eq_zero {f : MvPolynomial σ ℂ} (h : DegLt 0 f) : f = 0 := by
  ext α; simpa using h α (Nat.zero_le _)

omit [DecidableEq σ] in
theorem DegLt.mono {k k' : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (hk : k ≤ k') : DegLt k' f :=
  fun α hα => h α (hk.trans hα)

omit [DecidableEq σ] in
theorem DegLt.pderiv {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt (k + 1) f) (l : σ) : DegLt k (pderiv l f) :=
  fun α hα => by rw [coeff_pderiv, h _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul]

theorem DegLt.X_mul {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (l : σ) : DegLt (k + 1) (X l * f) :=
  fun α hα => by
    rw [coeff_X_mul']
    split_ifs with hl
    · refine h _ ?_
      have e : α - Finsupp.single l 1 + Finsupp.single l 1 = α :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl)))
      have := congrArg Finsupp.degree e
      rw [map_add (f := _), Finsupp.degree_single] at this
      omega
    · rfl

omit [DecidableEq σ] in
theorem DegLt.smul {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (c : ℂ) : DegLt k (c • f) :=
  fun α hα => by rw [coeff_smul, h α hα, smul_zero]

omit [DecidableEq σ] in
theorem DegLt.add {k : ℕ} {f g : MvPolynomial σ ℂ} (h : DegLt k f) (h' : DegLt k g) : DegLt k (f + g) :=
  fun α hα => by rw [MvPolynomial.coeff_add, h α hα, h' α hα, add_zero]

omit [DecidableEq σ] in
theorem DegLt.sum {k : ℕ} {I : Type} [Fintype I] {f : I → MvPolynomial σ ℂ} (h : ∀ i, DegLt k (f i)) :
    DegLt k (∑ i, f i) :=
  fun α hα => by rw [coeff_sum]; exact Finset.sum_eq_zero fun i _ => h i α hα

theorem inner_eq_sum (f g : MvPolynomial σ ℂ) :
    inner ℂ (F.ι f) (F.ι g) =
      ∑ α ∈ f.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff f α) * ((GlobalTheory.FockSeq.mfact α : ℂ) * AddMonoidAlgebra.coeff g α) := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e : (monomial α (AddMonoidAlgebra.coeff f α) : MvPolynomial σ ℂ) = AddMonoidAlgebra.coeff f α • monomial α 1 := by simp [smul_monomial]
  rw [e, map_smul, inner_smul_left, hasCoeff_coe F g α, GlobalTheory.FockSeq.mfact_cast, MvPolynomial.coeff_coe]

theorem coeff_X_mul_pderiv (l : σ) (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (X l * pderiv l f) α = (α l : ℂ) * AddMonoidAlgebra.coeff f α := by
  rw [coeff_X_mul']
  split_ifs with hl
  · have h0 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hl)
    rw [coeff_pderiv, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h0), mul_comm]
    simp [Nat.cast_sub h0]
  · simp [Finsupp.notMem_support_iff.1 hl]

theorem sum_sq_pderiv_le [Fintype σ] {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) :
    ∑ l, ‖F.ι (pderiv l f)‖ ^ 2 ≤ k * ‖F.ι f‖ ^ 2 := by
  have h1 : ∀ l, ‖F.ι (pderiv l f)‖ ^ 2 =
      ∑ α ∈ f.support, (α l : ℝ) * (GlobalTheory.FockSeq.mfact α * Complex.normSq (AddMonoidAlgebra.coeff f α)) := fun l => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), inner_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_X_mul_pderiv]
    simp [Complex.normSq_apply]; ring
  have h2 : ‖F.ι f‖ ^ 2 = ∑ α ∈ f.support, (GlobalTheory.FockSeq.mfact α * Complex.normSq (AddMonoidAlgebra.coeff f α)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp [Complex.normSq_apply]; ring
  simp only [h1, h2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
  rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, Nat.cast_le]
  exact le_of_not_ge fun hk => mem_support_iff.1 hα (h α hk)

theorem inner_X_X (a b : σ) (f g : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (X a * f)) (F.ι (X b * g)) =
      inner ℂ (F.ι (pderiv b f)) (F.ι (pderiv a g)) + if a = b then inner ℂ (F.ι f) (F.ι g) else 0 := by
  rw [GlobalTheory.Oscillator.inner_X_mul (isFockIP F), GlobalTheory.Oscillator.inner_pderiv (isFockIP F), Derivation.leibniz,
    map_add, inner_add_right, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem norm_X_mul_le [Fintype σ] {k : ℕ} {f : MvPolynomial σ ℂ} (h : DegLt k f) (l : σ) :
    ‖F.ι (X l * f)‖ ≤ √(k + 1) * ‖F.ι f‖ := by
  have h1 : ‖F.ι (X l * f)‖ ^ 2 = ‖F.ι (pderiv l f)‖ ^ 2 + ‖F.ι f‖ ^ 2 := by
    simp only [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_X_X, if_true, map_add (f := _)]
  have h2 : ‖F.ι (pderiv l f)‖ ^ 2 ≤ k * ‖F.ι f‖ ^ 2 :=
    (Finset.single_le_sum (f := fun l => ‖F.ι (pderiv l f)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ l)).trans (sum_sq_pderiv_le F h)
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith

end General

section Quad

variable {P Q : ℕ} (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ)

def quadMul (f : MvPolynomial (Ix P Q) ℂ) : MvPolynomial (Ix P Q) ℂ :=
  ∑ i, ∑ j, A i j • (X (Sum.inl i) * (X (Sum.inr j) * f))

def quadDer (f : MvPolynomial (Ix P Q) ℂ) : MvPolynomial (Ix P Q) ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (A i j) • pderiv (Sum.inr j) (pderiv (Sum.inl i) f)

theorem inner_quadMul (f g : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (quadMul A f)) (F.ι g) = inner ℂ (F.ι f) (F.ι (quadDer A g)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    GlobalTheory.Oscillator.inner_X_mul (isFockIP F)]

theorem inner_XX_XX (i k : Fin P) (j l : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (X (Sum.inl i) * (X (Sum.inr j) * f))) (F.ι (X (Sum.inl k) * (X (Sum.inr l) * f))) =
      inner ℂ (F.ι (pderiv (Sum.inr l) (pderiv (Sum.inl k) f))) (F.ι (pderiv (Sum.inr j) (pderiv (Sum.inl i) f))) +
      (if j = l then inner ℂ (F.ι (pderiv (Sum.inl k) f)) (F.ι (pderiv (Sum.inl i) f)) else 0) +
      (if i = k then inner ℂ (F.ι (pderiv (Sum.inr l) f)) (F.ι (pderiv (Sum.inr j) f)) else 0) +
      (if i = k then if j = l then inner ℂ (F.ι f) (F.ι f) else 0 else 0) := by
  have e : ∀ (a : Fin P) (b : Fin Q), pderiv (Sum.inl a : Ix P Q) ((X (Sum.inr b) : MvPolynomial (Ix P Q) ℂ) * f) =
      X (Sum.inr b) * pderiv (Sum.inl a) f := fun a b => by
    rw [Derivation.leibniz, pderiv_X_of_ne (by simp)]; simp
  rw [inner_X_X, e, e, inner_X_X, inner_X_X]
  simp only [Sum.inl.injEq, Sum.inr.injEq]
  split_ifs <;> simp [add_assoc]

theorem inner_quadMul_self (f : MvPolynomial (Ix P Q) ℂ) :
    inner ℂ (F.ι (quadMul A f)) (F.ι (quadMul A f)) = inner ℂ (F.ι (quadDer A f)) (F.ι (quadDer A f)) +
      ∑ k, ∑ i, (A * Aᴴ) k i * inner ℂ (F.ι (pderiv (Sum.inl k) f)) (F.ι (pderiv (Sum.inl i) f)) +
      ∑ l, ∑ j, (Aᴴ * A)ᵀ l j * inner ℂ (F.ι (pderiv (Sum.inr l) f)) (F.ι (pderiv (Sum.inr j) f)) +
      ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) * inner ℂ (F.ι f) (F.ι f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [quadMul, quadDer, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_XX_XX, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Complex.ofReal_sum, Complex.conj_conj,
    RCLike.star_def]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp_rw [← Fintype.sum_prod_type']
    exact Fintype.sum_bijective (fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1))
      (Function.Involutive.bijective fun _ => rfl) _ _ fun _ => mul_left_comm _ _ _
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [← mul_assoc, Complex.mul_conj]

theorem norm_quadMul_le {r : ℝ} (hr : 0 ≤ r)
    (h1 : ((r : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Aᴴ * A).PosSemidef)
    (h2 : ((r : ℂ) • (1 : Matrix (Fin P) (Fin P) ℂ) - A * Aᴴ).PosSemidef) (n : ℕ) :
    ∀ f, DegLt (2 * n) f →
      ‖F.ι (quadMul A f)‖ ≤ √(n * (∑ i, ∑ j, Complex.normSq (A i j)) + r * (n * (n + 1))) * ‖F.ι f‖ := by
  set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  induction n with
  | zero => intro f hf; simp [hf.eq_zero, quadMul]
  | succ n ih =>
    intro f hf
    have hD : DegLt (2 * n) (quadDer A f) :=
      DegLt.sum fun i => DegLt.sum fun j => ((DegLt.pderiv (k := 2 * n + 1) hf _).pderiv _).smul _
    have hc : 0 ≤ n * T + r * (n * (n + 1)) := by positivity
    have e1 : ‖F.ι (quadDer A f)‖ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι f‖ := by
      suffices h : ‖F.ι (quadDer A f)‖ * ‖F.ι (quadDer A f)‖ ≤
          √(n * T + r * (n * (n + 1))) * ‖F.ι f‖ * ‖F.ι (quadDer A f)‖ by
        rcases (norm_nonneg (F.ι (quadDer A f))).eq_or_lt with h0 | h0
        · rw [← h0]; positivity
        · exact le_of_mul_le_mul_right h h0
      rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ), ← inner_quadMul]
      refine (re_inner_le_norm _ _).trans ?_
      calc _ ≤ √(n * T + r * (n * (n + 1))) * ‖F.ι (quadDer A f)‖ * ‖F.ι f‖ :=
            mul_le_mul_of_nonneg_right (ih _ hD) (norm_nonneg _)
        _ = _ := by ring
    have e2 : ‖F.ι (quadDer A f)‖ ^ 2 ≤ (n * T + r * (n * (n + 1))) * ‖F.ι f‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) e1 2
      rwa [mul_pow, Real.sq_sqrt hc] at this
    have e3 := re_sum_inner_le h2 fun k => F.ι (pderiv (Sum.inl k) f)
    have e4 := re_sum_inner_le (M := (Aᴴ * A)ᵀ) (r := r) (by simpa using h1.transpose)
      fun k => F.ι (pderiv (Sum.inr k) f)
    have e5 := mul_le_mul_of_nonneg_left (sum_sq_pderiv_le F hf) hr
    rw [Fintype.sum_sum_type] at e5
    have e6 := congrArg Complex.re (inner_quadMul_self F A f)
    have e7 : ∀ v : F.H, (inner ℂ v v).re = ‖v‖ ^ 2 := fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, e7, e7, e7, ← hT] at e6
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    rw [mul_pow, Real.sq_sqrt (by positivity), e6]
    push_cast at e5 ⊢
    nlinarith

variable (x : Ix P Q → ℂ)

theorem gaussPoly_mul (f : MvPolynomial (Ix P Q) ℂ) :
    gaussPoly A x * f = quadMul A f + ∑ l, x l • (X l * f) := by
  simp only [gaussPoly, quadMul, add_mul, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

theorem degLt_pow (n : ℕ) : DegLt (2 * n + 1) (gaussPoly A x ^ n) := by
  induction n with
  | zero =>
    intro α hα
    rw [pow_zero, coeff_one, if_neg]
    rintro rfl
    simp at hα
  | succ n ih =>
    rw [pow_succ', gaussPoly_mul]
    exact (DegLt.sum fun i => DegLt.sum fun j => ((ih.X_mul _).X_mul _).smul _).add
      (DegLt.sum fun l => ((ih.X_mul _).mono (by omega)).smul _)

theorem summable_pow (h : (1 - Aᴴ * A).PosDef) :
    Summable fun n : ℕ => (n.factorial : ℂ)⁻¹ • F.ι (gaussPoly A x ^ n) := by
  obtain ⟨r, hr0, hr1, h1, h2⟩ := exists_bound h
  set T : ℝ := ∑ i, ∑ j, Complex.normSq (A i j) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  set C : ℝ := ∑ l, ‖x l‖ with hC
  let g : ℝ → ℝ := fun u => √(u * T + r * (1 + u)) + C * √(2 * u + u ^ 2)
  have hg : Continuous g := by fun_prop
  have hg0 : g 0 < 1 := by simpa [g, Real.sqrt_lt' one_pos] using hr1
  obtain ⟨s, hs0, hs1⟩ := exists_between hg0
  have hev := ((hg.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).eventually_lt_const hs0
  refine summable_of_ratio_norm_eventually_le hs1 (hev.mono fun n hn => ?_)
  have hd : DegLt (2 * (n + 1)) (gaussPoly A x ^ n) := (degLt_pow A x n).mono (by omega)
  have hm : (0 : ℝ) < n + 1 := by positivity
  have b1 := norm_quadMul_le F A hr0.le h1 h2 (n + 1) _ hd
  have b2 : ‖F.ι (∑ l, x l • (X l * gaussPoly A x ^ n))‖ ≤
      C * (√(((2 * (n + 1) : ℕ) : ℝ) + 1) * ‖F.ι (gaussPoly A x ^ n)‖) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hC, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_X_mul_le F hd l) (norm_nonneg _)
  have s1 : √(((n + 1 : ℕ) : ℝ) * T + r * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) =
      (n + 1) * √(1 / (n + 1) * T + r * (1 + 1 / (n + 1))) := by
    rw [← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    congr 1; push_cast; field_simp
  have s2 : √(((2 * (n + 1) : ℕ) : ℝ) + 1) = (n + 1) * √(2 * (1 / (n + 1)) + (1 / (n + 1)) ^ 2) := by
    rw [← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    congr 1; push_cast; field_simp
  have b3 : ‖F.ι (gaussPoly A x ^ (n + 1))‖ ≤ (n + 1) * (s * ‖F.ι (gaussPoly A x ^ n)‖) := by
    rw [pow_succ', gaussPoly_mul, map_add (f := _)]
    refine (norm_add_le_of_le b1 b2).trans ?_
    rw [← hT, s1, s2]
    calc _ = (n + 1) * (g (1 / (n + 1)) * ‖F.ι (gaussPoly A x ^ n)‖) := by simp only [g]; ring
      _ ≤ _ := by gcongr; exact hn.le
  rw [norm_smul, norm_smul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, Nat.factorial_succ]
  calc _ ≤ ((((n + 1) * n.factorial : ℕ) : ℝ))⁻¹ * ((n + 1) * (s * ‖F.ι (gaussPoly A x ^ n)‖)) := by gcongr
    _ = _ := by push_cast; field_simp

end Quad

theorem coeff_pow_eq_zero {σ : Type} {q : MvPolynomial σ ℂ} (hq : AddMonoidAlgebra.coeff q 0 = 0) (n : ℕ) :
    ∀ α : σ →₀ ℕ, α.degree < n → AddMonoidAlgebra.coeff (q ^ n) α = 0 := by
  classical
  induction n with
  | zero => intro α hα; omega
  | succ n ih =>
    intro α hα
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have e := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)
    rw [map_add (f := _)] at e
    by_cases h0 : p.2 = 0
    · rw [h0, hq, mul_zero]
    · have : p.2.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff _).1 h)
      rw [ih _ (by omega), zero_mul]

theorem hasCoeff_unique {σ : Type} [DecidableEq σ] (F : Fock σ) {v w : F.H} {c : MvPowerSeries σ ℂ}
    (hv : HasCoeff F v c) (hw : HasCoeff F w c) : v = w := by
  refine F.dense.eq_of_inner_right (𝕜 := ℂ) ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add (f := _), inner_add_left, hf, hg]
  | monomial α a =>
    have e : (monomial α a : MvPolynomial σ ℂ) = a • monomial α 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_left, inner_smul_left, hv α, hw α]

theorem existsUnique_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ),
    (1 - Aᴴ * A).PosDef → ∃! v : F.H, HasCoeff F v (expPS (gaussPoly A x)) := by
  intro P Q F A x h
  refine existsUnique_of_exists_of_unique ⟨∑' n : ℕ, (n.factorial : ℂ)⁻¹ • F.ι (gaussPoly A x ^ n), fun α => ?_⟩
    fun v w hv hw => hasCoeff_unique F hv hw
  have e := (innerSL ℂ (F.ι (monomial α 1))).map_tsum (summable_pow F A x h)
  simp only [innerSL_apply_apply, inner_smul_right, hasCoeff_coe F _ α, MvPolynomial.coeff_coe] at e
  rw [e, tsum_eq_sum (s := Finset.range (α.degree + 1)), MvPowerSeries.coeff_apply, expPS, Finset.mul_sum]
  · exact Finset.sum_congr rfl fun n _ => by ring
  · intro n hn
    rw [coeff_pow_eq_zero (coeff_zero_gaussPoly A x) n α (by simpa using hn), mul_zero, mul_zero]

end GlobalTheory.FockGauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_existsUnique_gaussian_vector : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → ∃! v : F.H, HasCoeff F v (expPS (gaussPoly A x)) := by
  first | exact @GlobalTheory.FockGauss.existsUnique_gauss | exact GlobalTheory.FockGauss.existsUnique_gauss | (intros; apply GlobalTheory.FockGauss.existsUnique_gauss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCover
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : F.H :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose

theorem hasCoeff_gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : HasCoeff F (gauss F h x) (expPS (gaussPoly A x)) :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose_spec

theorem gauss_congr (F : Fock (Ix P Q)) {A B : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (h' : (1 - Bᴴ * B).PosDef) {x y : Ix P Q → ℂ} (e : A = B) (e' : x = y) : gauss F h x = gauss F h' y := by
  subst e e'; rfl

abbrev Par (P Q : ℕ) : Type :=
  ℂ × {Y : Matrix (Ix P Q) (Fin Q) ℂ // IsNeg Y} × (Ix P Q → ℂ) × (Ix P Q → ℂ)

def vec (F : Fock (Ix P Q)) (p : Par P Q) : F.H :=
  (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) • gauss F p.2.1.2.posDef (linX p.2.1.1 p.2.2.1 p.2.2.2)

def act (T0 : GrpData P Q) (g : T0.G) (p : Par P Q) : Par P Q :=
  ((T0.sq g : ℂˣ) * p.1, ⟨(T0.cov g : Mat P Q) * p.2.1.1, p.2.1.2.mul (T0.cov_mem g)⟩,
    (T0.cov g : Mat P Q) *ᵥ p.2.2.1, p.2.2.2 ᵥ* (T0.cov g⁻¹ : Mat P Q))

def base (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : Par P Q :=
  (c, ⟨baseY A, isNeg_baseY h⟩, baseV x, baseF x)

theorem vec_base (F : Fock (Ix P Q)) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : vec F (base c h x) = c • gauss F h x := by
  simp only [vec, base, scal_base, mul_one]
  rw [gauss_congr F _ h (matA_baseY A) (linX_base A x)]

theorem inner_vec (F : Fock (Ix P Q)) (p q : Par P Q) :
    inner ℂ (vec F p) (vec F q) = star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨c, ⟨Y, hY⟩, v, φ⟩ := p
  obtain ⟨c', ⟨Y', hY'⟩, v', φ'⟩ := q
  have h1 := GlobalTheory.T.inner_gaussianVectors_fockSpace P Q F _ _ _ _ hY.posDef hY'.posDef _ _
    (hasCoeff_gauss F hY.posDef (linX Y v φ)) (hasCoeff_gauss F hY'.posDef (linX Y' v' φ'))
  have h2 := GlobalTheory.T.gaussian_inner_eq_invariantKernel P Q Y Y' v φ v' φ' hY.isUnit hY'.isUnit (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ hY.posDef hY'.posDef)
  simp only at h1 h2 ⊢
  simp only [vec, inner_smul_left, inner_smul_right, h1, ← h2, map_mul, starRingEnd_apply]
  ring

theorem isUnit_form {Y Y' : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) (h' : IsNeg Y') :
    IsUnit (Yᴴ * Jm P Q * Y').det := by
  have h1 : IsUnit (-(Yᴴ * Jm P Q * Y')).det := by
    rw [form_factor Y Y' h.isUnit h'.isUnit, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (h.isUnit.star.mul (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ h.posDef h'.posDef)).mul h'.isUnit
  rw [Matrix.det_neg] at h1
  exact isUnit_of_mul_isUnit_right h1

theorem dense_vec (F : Fock (Ix P Q)) : Dense (Submodule.span ℂ (Set.range (vec F)) : Set F.H) := by
  have h0 : (1 - (0 : Matrix (Fin P) (Fin Q) ℂ)ᴴ * (0 : Matrix (Fin P) (Fin Q) ℂ)).PosDef := by
    simpa using Matrix.PosDef.one
  refine (GlobalTheory.T.dense_span_coherent_vectors_fock P Q F (gauss F h0) (hasCoeff_gauss F h0)).mono (Submodule.span_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨base 1 h0 x, by rw [vec_base, one_smul]⟩

theorem exists_rep (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ π : T0.G →* (F.H →L[ℂ] F.H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (vec F p) = vec F (act T0 g p) := by
  have hc : Continuous fun g : T0.G => (T0.cov g : Mat P Q) :=
    Units.continuous_val.comp (continuous_fst.comp T0.emb.continuous)
  refine GlobalTheory.T.exists_unitaryRep_of_action_on_total_family T0.G (Par P Q) F.H (act T0) (vec F) (fun p => ?_) (fun g h p => ?_) (dense_vec F)
    (fun g p q => ?_) (fun p q => ?_)
  · simp [act]
  · simp [act, mul_assoc, Matrix.mul_assoc]
  · rw [inner_vec, inner_vec]
    simp only [act]
    rw [ker_mul (T0.cov_mem g) (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])]
    have h : star ((T0.sq g : ℂˣ) : ℂ) * (T0.sq g : ℂˣ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', RealPar.Cover.norm_sq]; simp
    rw [star_mul']
    linear_combination (star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2) * h
  · simp only [inner_vec]
    refine (continuous_const.mul (RealPar.Cover.continuous_sq.mul continuous_const)).mul
      (GlobalTheory.T.continuous_oscillatorGaussianKernel_right P Q T0.G _ _ _ _ _ _ ?_ ?_ ?_ fun g => isUnit_form q.2.1.2 (act T0 g p).2.1.2)
    · exact hc.matrix_mul continuous_const
    · exact hc.matrix_mulVec continuous_const
    · exact continuous_const.matrix_vecMul (hc.comp continuous_inv)

theorem hasDerivAt_exp_entry (X : Mat P Q) (a b : Ix P Q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem expt_inv (T0 : GrpData P Q) {Z : Mat P Q} (hZ : Z ∈ upq P Q) (t : ℝ) :
    (T0.expt (t • Z))⁻¹ = T0.expt (t • -Z) := by
  rw [inv_eq_iff_mul_eq_one, smul_neg, ← neg_smul, ← T0.expt_add Z hZ, add_neg_cancel, zero_smul, T0.expt_zero]

theorem neg_mem_upq {Z : Mat P Q} (hZ : Z ∈ upq P Q) : -Z ∈ upq P Q := by
  simpa using RealPar.KStabLie.smul_mem_upq hZ (-1)

theorem adjZ_neg {Z : Mat P Q} (hZ : Z ∈ upq P Q) : adjZ (-Z) = Z := by
  have h : Zᴴ * Jm P Q = -(Jm P Q * Z) := eq_neg_of_add_eq_zero_left hZ
  rw [adjZ, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem hasDerivAt_inner_act (T0 : GrpData P Q) (F : Fock (Ix P Q)) {Z : Mat P Q} (hZ : Z ∈ upq P Q)
    (f : MvPolynomial (Ix P Q) ℂ) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) :
    HasDerivAt (fun t : ℝ => inner ℂ (F.ι f) (vec F (act T0 (T0.expt (t • Z)) (base c h x))))
      (inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) (vec F (base c h x))) 0 := by
  set g : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z)) : Mat P Q) with hg
  set g' : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z))⁻¹ : Mat P Q) with hg'
  have g0 : g 0 = 1 := by simp [hg, T0.expt_zero]
  have g0' : g' 0 = 1 := by simp [hg', T0.expt_zero]
  obtain ⟨hA, hx, hs⟩ := GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity P Q A x Z g g' g0 g0'
    (fun a b => by
      simpa only [hg, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq hZ _)] using hasDerivAt_exp_entry Z a b)
    (fun a b => by
      simpa only [hg', expt_inv T0 hZ, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq (neg_mem_upq hZ) _), Matrix.neg_apply] using
        hasDerivAt_exp_entry (-Z) a b)
  have hn : ∀ t, IsNeg (g t * baseY A) := fun t => (isNeg_baseY h).mul (T0.cov_mem _)
  have hp := GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian P Q F _ _ (fun t => gauss F (hn t).posDef
    (linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t))) _ _ (fun t => hasCoeff_gauss F _ _) hA hx f
  have e0 : gauss F (hn 0).posDef (linX (g 0 * baseY A) (g 0 *ᵥ baseV x) (baseF x ᵥ* g' 0)) = gauss F h x :=
    gauss_congr F _ _ (by rw [g0, Matrix.one_mul, matA_baseY])
      (by rw [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base])
  obtain ⟨a1, a2⟩ := GlobalTheory.T.gaussianVector_annihilator_equations P Q F A x _ (hasCoeff_gauss F h x)
  have h5 := ((((RealPar.Cover.hasDerivAt_sq (T := T0) hZ).mul_const c).fun_mul hs).fun_mul hp)
  simp only [vec_base, inner_smul_right, GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial P Q F A x _ a1 a2 Z f]
  simp only [vec, inner_smul_right]
  refine h5.congr_deriv ?_
  simp only [e0]
  simp only [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, scal_base, zero_smul, T0.expt_zero,
    map_one, Units.val_one]
  ring

theorem exists_isOsc (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  obtain ⟨π, h1, h2, h3⟩ := exists_rep T0 F
  refine ⟨π, h1, h2, fun Z hZ f => ?_⟩
  refine GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set F.H (fun t => π (T0.expt (t • Z))) (Set.range (vec F)) _ _ ?_ (fun s t => ?_) (fun t => h1 _)
    (fun y => (h2 y).comp (T0.expt_cont.comp_continuous (by fun_prop)
      fun t => RealPar.KStabLie.smul_mem_upq hZ t)) (dense_vec F) ?_ ?_
  · simp [T0.expt_zero]
  · simp only [T0.expt_add Z hZ, map_mul]
  · rintro t _ ⟨p, rfl⟩
    exact ⟨_, (h3 _ p).symm⟩
  · rintro _ ⟨p, rfl⟩
    have e : vec F p = vec F (base (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)) := by rw [vec_base, vec]
    have h4 := hasDerivAt_inner_act T0 F (neg_mem_upq hZ) f (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)
    simp only [← h3, ← e, adjZ_neg hZ] at h4
    refine h4.congr_of_eventuallyEq (.of_forall fun t => ?_)
    have iso := (⟨(π (T0.expt (t • Z)) : F.H →ₗ[ℂ] F.H), h1 _⟩ : F.H →ₗᵢ[ℂ] F.H).inner_map_map (F.ι f)
      (π (T0.expt (t • -Z)) (vec F p))
    simp only [← iso]
    change _ = inner ℂ (π _ _) (π _ (π _ _))
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← expt_inv T0 hZ, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]

end GlobalTheory.OscGauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCoverStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover : ∀ (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)), ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  first | exact @GlobalTheory.OscGauss.exists_isOsc | exact GlobalTheory.OscGauss.exists_isOsc | (intros; apply GlobalTheory.OscGauss.exists_isOsc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

theorem nonempty_fockData_pair :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s),
      Nonempty (FockData T0 T1 T2) := by
  intro p q r s T0 T1 T2
  obtain ⟨Om, h⟩ := GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover _ _ T0 (GlobalTheory.Mem.Osc.seqFock _)
  exact GlobalTheory.Osc.nonempty_fockData_iff.2 ⟨h.toOsc⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_fockModel_unitary_dual_pair : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_pair | exact GlobalTheory.nonempty_fockData_pair | (intros; apply GlobalTheory.nonempty_fockData_pair <;> assumption)
end
