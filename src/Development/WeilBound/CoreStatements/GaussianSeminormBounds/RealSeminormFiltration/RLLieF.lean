module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieB

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieC
noncomputable section

open Complex Matrix Filter Topology

namespace PositivityTheory.RL.Up

theorem exp_mul_inj {z z' : ℂ} (h : ∀ t : ℝ, cexp (z * t) = cexp (z' * t)) : z = z' := by
  have d : ∀ z : ℂ, HasDerivAt (fun t : ℝ => cexp (z * t)) z 0 := fun z => by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul z).cexp
  have := d z
  simp only [h] at this
  exact this.unique (d z')

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

def expU (Z : 𝔸) : 𝔸ˣ :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  ⟨NormedSpace.exp Z, NormedSpace.exp (-Z),
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_right, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]⟩

theorem expU_add (Z : 𝔸) (s t : ℝ) : expU ((s + t) • Z) = expU (s • Z) * expU (t • Z) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  refine Units.ext ?_
  show NormedSpace.exp _ = NormedSpace.exp _ * NormedSpace.exp _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Z).smul_left s).smul_right t)]

theorem expU_zero : expU (0 : 𝔸) = 1 := Units.ext NormedSpace.exp_zero

theorem continuous_expU (Z : 𝔸) : Continuous fun t : ℝ => expU (t • Z) :=
  Units.isOpenEmbedding_val.isInducing.continuous_iff.2
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t).continuousAt)

end Banach

theorem eq_trace {β : Type} [Fintype β] [DecidableEq β] (ξ : Matrix β β ℂ →ₗ[ℂ] ℂ)
    (h : ∀ A B, ξ (A * B - B * A) = 0) : ∃ c : ℂ, ∀ A, ξ A = c * A.trace := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · exact ⟨0, fun A => by rw [Subsingleton.elim A 0, map_zero, zero_mul]⟩
  refine ⟨ξ (single b b 1), fun A => ?_⟩
  have h1 : ∀ i j, i ≠ j → ξ (single i j 1) = 0 := fun i j hij => by
    have := h (single i i 1) (single i j 1)
    rwa [single_mul_single_same, single_mul_single_of_ne (h := hij.symm), one_mul, sub_zero] at this
  have h2 : ∀ i, ξ (single i i 1) = ξ (single b b 1) := fun i => by
    have := h (single i b 1) (single b i 1)
    rwa [single_mul_single_same, single_mul_single_same, one_mul, map_sub, sub_eq_zero] at this
  conv_lhs => rw [matrix_eq_sum_single A]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ξ (single i j (A i j)) = A i j * ξ (single i j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [e, h1 i j hj.symm, mul_zero]) (by simp), e, h2, mul_comm]
  rfl

theorem real_form_trace {β : Type} [Fintype β] [DecidableEq β] (τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ)
    (hI : ∀ A, τ (I • A) = -(I • τ A)) (hτ : ∀ A, τ (τ A) = A) (ζ : Matrix β β ℂ →ₗ[ℝ] ℂ)
    (hb : ∀ X Y, τ X = X → τ Y = Y → τ (X * Y - Y * X) = X * Y - Y * X ∧ ζ (X * Y - Y * X) = 0) :
    ∃ c : ℂ, ∀ Z, τ Z = Z → ζ Z = c * Z.trace := by
  let P : Matrix β β ℂ → Matrix β β ℂ := fun A => (1 / 2 : ℝ) • (A + τ A)
  have hP : ∀ A, τ (P A) = P A := fun A => by simp only [P, map_smul, map_add (f := _), hτ, add_comm]
  let ξ0 : Matrix β β ℂ → ℂ := fun A => ζ (P A) - I * ζ (P (I • A))
  have add : ∀ A B, ξ0 (A + B) = ξ0 A + ξ0 B := fun A B => by
    simp only [ξ0, P, smul_add, map_add (f := _), map_smul]
    ring
  have rs : ∀ (r : ℝ) A, ξ0 (r • A) = r * ξ0 A := fun r A => by
    simp only [ξ0, P, smul_comm I r, smul_add, map_add (f := _), map_smul, real_smul]
    ring
  have is : ∀ A, ξ0 (I • A) = I * ξ0 A := fun A => by
    simp only [ξ0, P, smul_smul, I_mul_I, neg_smul, one_smul, smul_add, map_add (f := _), map_smul, map_neg, real_smul, smul_neg]
    linear_combination ((((1 / 2 : ℝ) : ℂ) * ζ (I • A) + ((1 / 2 : ℝ) : ℂ) * ζ (τ (I • A)))) * I_mul_I
  let ξ : Matrix β β ℂ →ₗ[ℂ] ℂ :=
    { toFun := ξ0
      map_add' := add
      map_smul' := fun c A => by
        have e : c • A = c.re • A + I • (c.im • A) := by
          ext i j
          simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
          linear_combination (-A i j) * re_add_im c
        rw [e, add, is, rs, rs, RingHom.id_apply, smul_eq_mul]
        linear_combination (ξ0 A) * re_add_im c }
  have fix : ∀ Z, τ Z = Z → ξ Z = ζ Z := fun Z hZ => by
    have e1 : P Z = Z := by
      simp only [P, hZ]
      module
    have e2 : P (I • Z) = 0 := by simp only [P, hI, hZ, add_neg_cancel, smul_zero]
    show ζ (P Z) - I * ζ (P (I • Z)) = _
    rw [e1, e2, map_zero, mul_zero, sub_zero]
  have dec : ∀ A, A = P A - I • P (I • A) := fun A => by
    simp only [P, hI]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, real_smul]
    push_cast
    linear_combination ((A i j - τ A i j) / 2) * I_mul_I
  have br : ∀ X Y, τ X = X → τ Y = Y → ξ (X * Y - Y * X) = 0 := fun X Y hX hY => by
    rw [fix _ (hb X Y hX hY).1, (hb X Y hX hY).2]
  obtain ⟨c, hc⟩ := eq_trace ξ fun A B => by
    have h1 : ∀ X, τ X = X → ξ (X * B - B * X) = 0 := fun X hX => by
      have e : X * B - B * X = (X * P B - P B * X) - I • (X * P (I • B) - P (I • B) * X) := by
        conv_lhs => rw [dec B]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        abel
      rw [e, map_sub, map_smul, br _ _ hX (hP _), br _ _ hX (hP _), smul_zero, sub_zero]
    have e : A * B - B * A = (P A * B - B * P A) - I • (P (I • A) * B - B * P (I • A)) := by
      conv_lhs => rw [dec A]
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, map_sub, map_smul, h1 _ (hP _), h1 _ (hP _), smul_zero, sub_zero]
  exact ⟨c, fun Z hZ => by rw [← fix Z hZ, hc]⟩

end PositivityTheory.RL.Up

end
end

noncomputable section

open Complex Matrix Filter Topology
open scoped Real RealInnerProductSpace

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem lie_of_exp_banach {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸]
    [StarModule ℝ 𝔸] (Z K : 𝔸) (h : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) * K * NormedSpace.exp (t • Z) = K) :
    star Z * K + K * Z = 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  have hP := (hE.star.mul (hasDerivAt_const (0 : ℝ) K)).mul hE
  have hf : ((fun u : ℝ => star (NormedSpace.exp (u • Z))) * (fun _ : ℝ => K)) *
      (fun u : ℝ => NormedSpace.exp (u • Z)) = fun _ => K := by
    funext u
    simp only [Pi.mul_apply]
    exact h u
  rw [hf] at hP
  have e := hP.unique (hasDerivAt_const (0 : ℝ) K)
  simpa [NormedSpace.exp_zero] using e

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {𝕜 ι : Type} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (Z K : Matrix ι ι 𝕜)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * K * NormedSpace.exp (t • Z) = K) : Zᴴ * K + K * Z = 0 := by
  exact @lie_of_exp_banach (Matrix ι ι 𝕜) _ _ _ _ ⟨continuous_id.matrix_conjTranspose⟩ _ Z K h

variable {l : Type} [Fintype l] [DecidableEq l]

theorem sympl_eq (w w' : l ⊕ l → ℝ) : sympl w w' = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ w') := by
  simp [sympl, pPart, qPart, dotProduct, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_mulVec,
    PiLp.inner_apply, Finset.sum_sub_distrib, Matrix.neg_mulVec, Matrix.one_mulVec, Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

theorem mem_sp_of (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ w w', sympl (A *ᵥ w) (A *ᵥ w') = sympl w w') :
    A ∈ Matrix.symplecticGroup l ℝ := by
  have key : ∀ v u : l ⊕ l → ℝ, (A *ᵥ v) ⬝ᵥ Matrix.J l ℝ *ᵥ (A *ᵥ u) = v ⬝ᵥ (Aᵀ * Matrix.J l ℝ * A) *ᵥ u := by
    intro v u
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff']
  ext i j
  have e := h (Pi.single i 1) (Pi.single j 1)
  rw [sympl_eq, sympl_eq, neg_inj, key] at e
  simpa [Matrix.mulVec_single_one, Pi.single_apply, dotProduct, Matrix.mulVec] using e

theorem mem_lie_of (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  have := lie_of_exp X (Matrix.J l ℝ) fun t => by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact SymplecticGroup.mem_iff'.1 (h t)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
  show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X
  rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero, this]

variable {W β : Type} [Fintype W] [DecidableEq W] [Fintype β] [DecidableEq β]

def SG (K : W → Matrix β β ℂ) : Subgroup (W → Matrix β β ℂ)ˣ where
  carrier := {g | star g.1 * K * g.1 = K}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : star a.1 * K * a.1 = K := ha
    have hb' : star b.1 * K * b.1 = K := hb
    show star (a.1 * b.1) * K * (a.1 * b.1) = K
    calc _ = star b.1 * (star a.1 * K * a.1) * b.1 := by simp only [star_mul, mul_assoc]
      _ = K := by rw [ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : star a.1 * K * a.1 = K := ha
    show star a⁻¹.1 * K * a⁻¹.1 = K
    calc _ = star a⁻¹.1 * (star a.1 * K * a.1) * a⁻¹.1 := by rw [ha']
      _ = star (a.1 * a⁻¹.1) * K * (a.1 * a⁻¹.1) := by simp only [star_mul, mul_assoc]
      _ = K := by simp

def LG (K : W → Matrix β β ℂ) : Submodule ℝ (W → Matrix β β ℂ) where
  carrier := {Z | star Z * K + K * Z = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have ha' : star a * K + K * a = 0 := ha
    have hb' : star b * K + K * b = 0 := hb
    show star (a + b) * K + K * (a + b) = 0
    rw [star_add, add_mul, mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' := fun r a ha => by
    have ha' : star a * K + K * a = 0 := ha
    show star (r • a) * K + K * (r • a) = 0
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha', smul_zero]

end PositivityTheory.RL.Up

end
