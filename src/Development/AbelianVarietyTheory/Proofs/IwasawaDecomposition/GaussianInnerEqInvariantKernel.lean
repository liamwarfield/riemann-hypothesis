module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem kerAlg_exponent {P Q : ℕ} (B : Matrix (Fin P) (Fin Q) ℂ) (C : Matrix (Fin Q) (Fin P) ℂ)
    (h : IsUnit (1 - C * B).det) (a c : Fin P → ℂ) (b d s u : Fin Q → ℂ) :
    -(b ⬝ᵥ s) + -(d ⬝ᵥ u) + (a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
      + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) =
    ((a + s ᵥ* C) ⬝ᵥ (c + B *ᵥ u) - s ⬝ᵥ u) -
      (a ᵥ* B + d - s ᵥ* (1 - C * B)) ⬝ᵥ (1 - C * B)⁻¹ *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) := by
  have h1 := Matrix.nonsing_inv_mul _ h
  have h2 := Matrix.mul_nonsing_inv _ h
  generalize (1 - C * B)⁻¹ = N at h1 h2 ⊢
  have h3 : C * B * N = N - 1 := by rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  have h4 : N * (C * B) = N - 1 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hM : (1 - B * C)⁻¹ = 1 + B * N * C := by
    apply Matrix.inv_eq_right_inv
    have : B * C * (B * N * C) = B * (C * B * N) * C := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, this, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_one]
    abel
  have hMB : (1 + B * N * C) * B = B * N := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hM, hMB]
  have e1 : N *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) = u - N *ᵥ (b + C *ᵥ c) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_neg]; abel
  have e2 : (s ᵥ* (1 - C * B)) ⬝ᵥ N *ᵥ (b + C *ᵥ c) = s ⬝ᵥ (b + C *ᵥ c) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e1, dotProduct_sub, sub_dotProduct _ _ (N *ᵥ _), e2]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, ← Matrix.dotProduct_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_comm b s]
  ring

theorem kerAlg_proj {P Q : ℕ} (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det)
    (h' : IsUnit Y'.toRows₂.det) :
    Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q =
      Matrix.fromRows (matA Y') 1 * (1 - (matA Y)ᴴ * matA Y')⁻¹ * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
  have hH : IsUnit (Y.toRows₂ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h.star
  have e0 : Yᴴ * Jm P Q * Y' = (-Y.toRows₂ᴴ) * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
    rw [Matrix.neg_mul, Matrix.neg_mul, ← form_factor Y Y' h h', neg_neg]
  have e1 : Yᴴ * Jm P Q = (-Y.toRows₂ᴴ) * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
    conv_lhs => rw [frame_eq Y h]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, baseY, Jm, Formalism.UG.Jpq,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.neg_mul,
      ← Matrix.mul_neg]
    congr 1
    ext i (j | j) <;> simp
  have hN : IsUnit (-Y.toRows₂ᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det] at hH ⊢; exact hH.neg
  rw [e0, Matrix.mul_assoc _ Yᴴ, e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e2 := frame_eq Y' h'
  generalize matA Y' = B at e2 ⊢
  generalize Y'.toRows₂ = Z at e2 h' ⊢
  subst e2
  simp only [Matrix.mul_assoc, baseY]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h', Matrix.nonsing_inv_mul_cancel_left _ _ hN]

theorem kerAlg : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  intro P Q Y Y' v φ v' φ' h h' hK A B a b c d M N
  have hs : star (scal Y v φ) = ((Y.toRows₂ᴴ).det)⁻¹ * Complex.exp (-(b ⬝ᵥ star (v ∘ Sum.inr))) := by
    rw [scal, star_mul', star_inv₀, Matrix.det_conjTranspose, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [b, dotProduct]
  have hs' : scal Y' v' φ' = (Y'.toRows₂.det)⁻¹ * Complex.exp (-(d ⬝ᵥ (v' ∘ Sum.inr))) := rfl
  have ha : star (v ∘ Sum.inl) = a + star (v ∘ Sum.inr) ᵥ* Aᴴ := by
    have : a = star (v ∘ Sum.inl - A *ᵥ (v ∘ Sum.inr)) := rfl
    rw [this, star_sub, Matrix.star_mulVec]; abel
  have hb : b = Aᴴ *ᵥ star (φ ∘ Sum.inl) + star (φ ∘ Sum.inr) := by
    have : b = star ((φ ∘ Sum.inl) ᵥ* A + φ ∘ Sum.inr) := rfl
    rw [this, star_add, Matrix.star_vecMul]
  have hc : v' ∘ Sum.inl = c + B *ᵥ (v' ∘ Sum.inr) := by
    have : c = v' ∘ Sum.inl - B *ᵥ (v' ∘ Sum.inr) := rfl
    rw [this]; abel
  have hd : d = (φ' ∘ Sum.inl) ᵥ* B + φ' ∘ Sum.inr := rfl
  have hJ1 : star v ᵥ* Jm P Q = Sum.elim (star (v ∘ Sum.inl)) (-star (v ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [Matrix.vecMul_neg]
  have hJ2 : Jm P Q *ᵥ star φ = Sum.elim (star (φ ∘ Sum.inl)) (-star (φ ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec]
    ext (i | i) <;> simp [Matrix.neg_mulVec]
  have e0 : (star v ᵥ* Jm P Q) ⬝ᵥ v' = (a + star (v ∘ Sum.inr) ᵥ* Aᴴ) ⬝ᵥ (c + B *ᵥ (v' ∘ Sum.inr))
      - star (v ∘ Sum.inr) ⬝ᵥ (v' ∘ Sum.inr) := by
    rw [← ha, ← hc, hJ1]
    simp [dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
  have e1 : (star v ᵥ* Jm P Q + φ') ᵥ* Matrix.fromRows B 1 =
      a ᵥ* B + d - star (v ∘ Sum.inr) ᵥ* (1 - Aᴴ * B) := by
    have : star v ᵥ* Jm P Q + φ' = Sum.elim (star (v ∘ Sum.inl) + φ' ∘ Sum.inl)
        (-star (v ∘ Sum.inr) + φ' ∘ Sum.inr) := by
      rw [hJ1]; ext (i | i) <;> rfl
    rw [this, Matrix.sumElim_vecMul_fromRows, ha, hd]
    simp only [Matrix.add_vecMul, Matrix.vecMul_one, Matrix.vecMul_sub, Matrix.vecMul_vecMul]
    abel
  have e2 : Matrix.fromCols (-Aᴴ) 1 *ᵥ (Jm P Q *ᵥ star φ + v') =
      -(b + Aᴴ *ᵥ c) + (1 - Aᴴ * B) *ᵥ (v' ∘ Sum.inr) := by
    have : Jm P Q *ᵥ star φ + v' = Sum.elim (star (φ ∘ Sum.inl) + v' ∘ Sum.inl)
        (-star (φ ∘ Sum.inr) + v' ∘ Sum.inr) := by
      rw [hJ2]; ext (i | i) <;> rfl
    rw [this, Matrix.fromCols_mulVec_sumElim, hb]
    conv_lhs => rw [hc]
    simp only [Matrix.mulVec_add, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.neg_mulVec,
      Matrix.neg_mul]
    abel
  have key := kerAlg_exponent B Aᴴ hK a c b d (star (v ∘ Sum.inr)) (v' ∘ Sum.inr)
  rw [ker, kerAlg_proj Y Y' h h', form_factor Y Y' h h', ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _ * _),
    ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _), Matrix.dotProduct_mulVec _ (Matrix.fromRows _ _), e0, e1, e2,
    ← key, hs, hs', Complex.exp_add (-_ + -_), Complex.exp_add (-_) (-_), Matrix.det_mul, Matrix.det_mul]
  simp only [mul_inv, M, N, A, B]
  ring

end GlobalTheory.OscGauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_inner_eq_invariantKernel : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  first | exact @GlobalTheory.OscGauss.kerAlg | exact GlobalTheory.OscGauss.kerAlg | (intros; apply GlobalTheory.OscGauss.kerAlg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentityStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentity
open Matrix

namespace GlobalTheory.Mem.InvDer

theorem hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM
  rw [h0, adjugate_one, Matrix.one_mul] at hd
  have hdet0 : (M 0).det = 1 := by rw [h0, det_one]
  have hne : (M 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det := hasDerivAt_inv hne
    have h2 := h1.comp_of_eq (0 : ℝ) hd rfl
    refine HasDerivAt.congr_deriv h2 ?_
    rw [hdet0]; simp
  refine ⟨hinv, ?_⟩
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0 := by
    intro i j
    have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0 := by
      have := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1))
        (M'.updateRow j 0) 0 (by
          intro a b
          by_cases h : a = j
          · simp only [updateRow_apply, h, if_true]
            exact hasDerivAt_const _ _
          · simp only [updateRow_apply, h, if_false]
            exact hM a b)
      simpa only [adjugate_apply] using this.differentiableAt
    have := hinv.differentiableAt.mul hadj
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  have hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0 := hd.continuousAt.eventually_ne hne
  have hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j)
      (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))
  have hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  have huniq := hprod.unique hconst
  rw [h0, inv_one, Finset.sum_add_distrib] at huniq
  simp [Matrix.one_apply] at huniq
  have hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j := eq_neg_of_add_eq_zero_left huniq
  rw [← hfin]
  exact (hdiff i j).hasDerivAt

end GlobalTheory.Mem.InvDer
end

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity : ∀ (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (M' : Matrix (Fin n) (Fin n) ℂ), M 0 = 1 → (∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) → HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧ ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  first | exact @GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | exact GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv | (intros; apply GlobalTheory.Mem.InvDer.hasDerivAt_inv_det_and_inv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss.ParDer

variable {l m n : Type} [Fintype m]

theorem der_mul {M : ℝ → Matrix l m ℂ} {N : ℝ → Matrix m n ℂ} {M' : Matrix l m ℂ} {N' : Matrix m n ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hN : ∀ i j, HasDerivAt (fun t => N t i j) (N' i j) s)
    (i : l) (j : n) : HasDerivAt (fun t => (M t * N t) i j) ((M' * N s + M s * N') i j) s := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).fun_mul (hN k j)

theorem der_dot {u v : ℝ → m → ℂ} {u' v' : m → ℂ} {s : ℝ}
    (hu : ∀ i, HasDerivAt (fun t => u t i) (u' i) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) :
    HasDerivAt (fun t => u t ⬝ᵥ v t) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hu k).fun_mul (hv k)

theorem der_mulVec {M : ℝ → Matrix l m ℂ} {v : ℝ → m → ℂ} {M' : Matrix l m ℂ} {v' : m → ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s)
    (i : l) : HasDerivAt (fun t => (M t *ᵥ v t) i) ((M' *ᵥ v s + M s *ᵥ v') i) s :=
  der_dot (u := fun t => M t i) (u' := M' i) (hM i) hv

theorem der_vecMul {M : ℝ → Matrix m n ℂ} {v : ℝ → m → ℂ} {M' : Matrix m n ℂ} {v' : m → ℂ} {s : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (j : n) : HasDerivAt (fun t => (v t ᵥ* M t) j) ((v' ᵥ* M s + v s ᵥ* M') j) s :=
  der_dot (v := fun t i => M t i j) (v' := fun i => M' i j) hv fun i => hM i j

theorem par_deriv : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  intro P Q A x Z g g' h0 h0' hg hg'
  have hY : ∀ i j, HasDerivAt (fun t => (g t * baseY A) i j) ((Z * baseY A) i j) 0 := fun i j => by
    simpa using der_mul (N := fun _ => baseY A) (N' := 0) hg (fun _ _ => hasDerivAt_const _ _) i j
  have hZ : Z * baseY A = Matrix.fromRows (Z.toBlocks₁₁ * A + Z.toBlocks₁₂) (Z.toBlocks₂₁ * A + Z.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Z, baseY, Matrix.fromBlocks_mul_fromRows]
    simp
  have hY1 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₁ i j) ((Z.toBlocks₁₁ * A + Z.toBlocks₁₂) i j) 0 :=
    fun i j => by have := hY (.inl i) j; rw [hZ] at this; exact this
  have hY2 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₂ i j) ((Z.toBlocks₂₁ * A + Z.toBlocks₂₂) i j) 0 :=
    fun i j => by have := hY (.inr i) j; rw [hZ] at this; exact this
  have e2 : (g 0 * baseY A).toRows₂ = 1 := by rw [h0, Matrix.one_mul]; rfl
  have e1 : (g 0 * baseY A).toRows₁ = A := by rw [h0, Matrix.one_mul]; rfl
  obtain ⟨hdet, hinv⟩ := GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity Q (fun t => (g t * baseY A).toRows₂) _ e2 hY2
  have hA : ∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0 := fun i j => by
    have := der_mul (N' := -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂)) hY1 hinv i j
    rw [e1, e2, inv_one, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg] at this
    exact this
  have eA : matA (g 0 * baseY A) = A := by rw [h0, Matrix.one_mul, matA_baseY]
  have hv : ∀ i, HasDerivAt (fun t => (g t *ᵥ baseV x) i) ((Z *ᵥ baseV x) i) 0 := fun i => by
    simpa using der_mulVec (v := fun _ => baseV x) (v' := 0) hg (fun _ => hasDerivAt_const _ _) i
  have hf : ∀ i, HasDerivAt (fun t => (baseF x ᵥ* g' t) i) ((baseF x ᵥ* (-Z)) i) 0 := fun i => by
    simpa using der_vecMul (v := fun _ => baseF x) (v' := 0) (M' := -Z) (fun _ => hasDerivAt_const _ _) hg' i
  have hv1 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inl) i) ((Z.toBlocks₁₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inl i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₁₁])
  have hv2 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inr) i) ((Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inr i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf1 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inl) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₁)) i) 0 :=
    fun i => (hf (.inl i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf2 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inr) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₂)) i) 0 :=
    fun i => (hf (.inr i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₂])
  have ev : (g 0 *ᵥ baseV x) ∘ Sum.inr = 0 := by rw [h0, Matrix.one_mulVec]; rfl
  have ef : (baseF x ᵥ* g' 0) ∘ Sum.inl = 0 := by rw [h0', Matrix.vecMul_one]; rfl
  have hX : ∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0 := by
    rintro (i | j)
    · refine ((hv1 i).fun_sub (der_mulVec hA hv2 i)).congr_deriv ?_
      rw [ev, eA]
      simp [dX, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    · refine ((der_vecMul hf1 hA j).fun_add (hf2 j)).congr_deriv ?_
      rw [ef, eA]
      simp [dX, Matrix.vecMul_add, Matrix.neg_vecMul, Matrix.vecMul_vecMul, add_comm]
  refine ⟨hA, hX, ?_⟩
  have hd := der_dot (u := fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) ∘ Sum.inr)
    (u' := dX Z A x ∘ Sum.inr) (fun j => hX (.inr j)) hv2
  refine (hdet.fun_mul hd.fun_neg.cexp).congr_deriv ?_
  simp only [ev, e2]
  rw [h0, h0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base]
  simp [dS, sub_eq_add_neg]

end GlobalTheory.OscGauss.ParDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  first | exact @GlobalTheory.OscGauss.ParDer.par_deriv | exact GlobalTheory.OscGauss.ParDer.par_deriv | (intros; apply GlobalTheory.OscGauss.ParDer.par_deriv <;> assumption)
end
end
