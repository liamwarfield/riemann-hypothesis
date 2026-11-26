module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivA
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cd

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

lemma cm_iff {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} :
    ContDiffAt ℝ n F x ↔ ∀ i j, ContDiffAt ℝ n (fun y => F y i j) x :=
  (contDiffAt_pi (Φ := F)).trans (forall_congr' fun _ => contDiffAt_pi)

lemma cm_mul {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by
  rw [cm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma c_det {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by
  rw [cm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hF _ _)

lemma cm_updateRow {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (j : Fin a)
    (b : Fin a → ℂ) : ContDiffAt ℝ n (fun y => (F y).updateRow j b) x := by
  rw [cm_iff] at hF ⊢
  intro i l
  by_cases hi : i = j
  · subst hi; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne hi]; exact hF i l

lemma cm_inv {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (hu : (F x).det ≠ 0) :
    ContDiffAt ℝ n (fun y => (F y)⁻¹) x := by
  rw [cm_iff]
  intro i j
  have e : (fun y => (F y)⁻¹ i j)
      = fun y => ((F y).det)⁻¹ * ((F y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((c_det hF).inv hu).mul (c_det (cm_updateRow hF j _))

lemma cm_conjT {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y)ᴴ) x := by
  rw [cm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp x (hF j i)

lemma contDiffAt_block_matrix_two {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by
  rw [cm_iff] at hA hB hC hD ⊢
  intro i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

lemma contDiffAt_block_matrix_three {k j ρ : ℕ} {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : X → B.Mat k ρ}
    {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : X → Matrix (Fin j) (Fin j) ℂ}
    {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : ContDiffAt ℝ n A11 x) (h12 : ContDiffAt ℝ n A12 x) (h13 : ContDiffAt ℝ n A13 x)
    (h21 : ContDiffAt ℝ n A21 x) (h22 : ContDiffAt ℝ n A22 x) (h23 : ContDiffAt ℝ n A23 x)
    (h31 : ContDiffAt ℝ n A31 x) (h32 : ContDiffAt ℝ n A32 x) (h33 : ContDiffAt ℝ n A33 x) :
    ContDiffAt ℝ n (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y)) x := by
  rw [cm_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

end cd

section hd

variable {t : ℝ}

lemma hd_iff {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t :=
  (hasDerivAt_pi (φ := F)).trans (forall_congr' fun _ => hasDerivAt_pi)

lemma hd_mul {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by
  rw [hd_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hF i l).mul (hG l j)

lemma hasDerivAt_block_matrix_three {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by
  rw [hd_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

lemma hd_invT {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by
  have hL : HasDerivAt (fun t : ℝ => (1 + t • B)ᴴ) Bᴴ 0 := by
    have e : (fun t : ℝ => (1 + t • B)ᴴ) = fun t => 1 + t • Bᴴ := by
      funext t; simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    rw [e]
    exact (((hasDerivAt_id' (0 : ℝ)).smul_const Bᴴ).const_add (1 : Matrix (Fin a) (Fin a) ℂ)).congr_deriv (one_smul _ _)
  have hC : ContDiffAt ℝ 1 (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 :=
    cm_inv (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))) (by simp)
  have hCd := (hC.differentiableAt one_ne_zero).hasDerivAt
  have hP := hd_mul hCd hL
  have hcont : ContinuousAt (fun t : ℝ => ((1 + t • B)ᴴ).det) 0 :=
    (c_det (n := 0) (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))).continuousAt
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 + t • B)ᴴ).det ≠ 0 := hcont.eventually_ne (by simp)
  have hev : (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  have h0 : HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin a) (Fin a) ℂ)).congr_of_eventuallyEq hev
  have hu := h0.unique hP
  simp only [zero_smul, add_zero, Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Matrix.one_mul] at hu
  have : deriv (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 = -Bᴴ := eq_neg_of_add_eq_zero_left hu.symm
  exact hCd.congr_deriv this

end hd

end PI.UnitaryGroupMassFormula.UsCost.DA
end
end

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA

lemma leviDifferential_add (k j ρ : ℕ) (Q Q' : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (Q + Q') = dmuP k j ρ Q + dmuP k j ρ Q' := by
  unfold dmuP
  rw [P.Ux4.block3_add]
  simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, add_zero, neg_add]

lemma leviDifferential_smul (k j ρ : ℕ) (c : ℝ) (Q : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (c • Q) = c • dmuP k j ρ Q := by
  unfold dmuP
  apply P.Ux4.ext_eB
  rintro (((a | a) | a)) (((b | b) | b)) <;>
    simp [P.Ux4.block3_apply, Matrix.conjTranspose_smul]

lemma block_matrix_two_zero_add {p s : ℕ} (e e' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (e + e') = blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e + blk2 0 0 0 e' := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma block_matrix_two_zero_smul {p s : ℕ} (c : ℝ) (e : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (c • e) = c • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma symmetricScalarBlockMatrix_one_zero {p s : ℕ} : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

lemma block_matrix_two_line {p s : ℕ} (t : ℝ) (A : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 + t • A) = 1 + t • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 A := by
  rw [← symmetricScalarBlockMatrix_one_zero]
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

def lamZ (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (e : Matrix (Fin s) (Fin s) ℂ) :
    B.Mat k (p + s + ρ) :=
  (Rn k (p + s) ρ ξ.1.2)⁻¹ *
    dmuP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
      blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
    Rn k (p + s) ρ ξ.1.2

def lamL (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) :
    Matrix (Fin s) (Fin s) ℂ →ₗ[ℝ] B.Mat k (p + s + ρ) where
  toFun := lamZ k ρ ξ
  map_add' e e' := by
    simp only [lamZ, block_matrix_two_zero_add, Matrix.mul_add, Matrix.add_mul, leviDifferential_add]
  map_smul' c e := by
    simp only [lamZ, block_matrix_two_zero_smul, Matrix.mul_smul, Matrix.smul_mul, leviDifferential_smul, RingHom.id_apply]

lemma coef_sum {s : ℕ} (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • eMat i.1 i.2.1 i.2.2 = (Matrix.of Z)⁻¹ * Matrix.of W := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, eMat, Matrix.of_apply]
  simp [Fintype.sum_prod_type, smul_ite, ite_and, Finset.sum_ite_eq, coefZ,
    Complex.real_smul, Complex.re_add_im]

lemma sum_dirZ {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • dirZ k ρ ξ i = lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
  rw [← coef_sum Z W]
  change _ = lamL k ρ ξ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]
  rfl

lemma rn_mem (hRad : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have h : Rn k j ρ x ∈ Rset k j ρ := (hRad k j ρ).2.1 ▸ Set.mem_range_self x
  exact h.1

lemma ga_mem (hMem : SliceMem) (hRad : RadicalParam) {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s} {γ : B.Mat k ρ} (hZ : G.detM Z ≠ 0)
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  have hdet : (ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [P.level_determinant_z]
    refine mul_ne_zero ?_ hZ
    rw [hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (P.Ux5.det_permutationMatrix_ne_zero σ) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  exact P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv (rn_mem hRad _ _ _ _)) ((hMem k (p + s) ρ).1 _ γ hdet hγ))
    (rn_mem hRad _ _ _ _)

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

lemma phi_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (Z' : G.Mat s) :
    gaXi k ρ σ d ξ Z' γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z') * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
      Rn k (p + s) ρ ξ.1.2) := by
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have := hSZ k p s ρ σ d ξ Z ((Matrix.of Z)⁻¹ * Matrix.of Z') γ
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mul] at this
  exact this

lemma U_inv_mul {p s : ℕ} (b : Fin p → Fin s → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
      blk2 1 (Matrix.of b) 0 1 = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [P.Ux4.block2_det_upper_triangular]
  simp

lemma line_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (W : G.Mat s)
    (t : ℝ) :
    gaXi k ρ σ d ξ (Z + t • W) γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ (1 + t • ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1)) *
      Rn k (p + s) ρ ξ.1.2) := by
  rw [phi_rep hSZ ξ hZ γ (Z + t • W)]
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have e1 : (Matrix.of Z)⁻¹ * Matrix.of (Z + t • W) = 1 + t • ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have : Matrix.of (Z + t • W) = Matrix.of Z + t • Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.nonsing_inv_mul _ hZu, Matrix.mul_smul]
  rw [e1, block_matrix_two_line, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, U_inv_mul, Matrix.mul_smul, Matrix.smul_mul]

end PI.UnitaryGroupMassFormula.UsCost.DB
end
end

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UnitaryGroupMassFormula.UsCost.DA PI.UnitaryGroupMassFormula.UsCost.DB

theorem zDeriv : ZDeriv := by
  intro hMem hRad hSZ k p s ρ σ d hd E _ _ H hH ξ Z γ hZ hγ W
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have hg := ga_mem hMem hRad hd ξ hZ hγ

  have hΦ : ContDiffAt ℝ 1 (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
    rw [show (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) = _ from funext (phi_rep hSZ ξ hZ γ)]
    have hA : ContDiffAt ℝ 1 (fun Z' : G.Mat s => (Matrix.of Z)⁻¹ * Matrix.of Z') Z :=
      cm_mul contDiffAt_const contDiffAt_id
    have hP := cm_mul (cm_mul (contDiffAt_const (c := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0
      (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹))
      (contDiffAt_block_matrix_two (contDiffAt_const (c := (1 : Matrix (Fin p) (Fin p) ℂ))) (contDiffAt_const (c := (0 : Matrix (Fin p) (Fin s) ℂ)))
        (contDiffAt_const (c := (0 : Matrix (Fin s) (Fin p) ℂ))) hA))
      (contDiffAt_const (c := blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ)))
    have hP1 : (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1 = 1 := by
      rw [Matrix.nonsing_inv_mul _ hZu, symmetricScalarBlockMatrix_one_zero, Matrix.mul_one, U_inv_mul]
    have hdet : ((((blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1))ᴴ).det ≠ 0 := by
      rw [hP1]; simp
    have hmu := contDiffAt_block_matrix_three (k := k) (ρ := ρ) hP (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (contDiffAt_const (c := (1 : B.Mat k ρ))) (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (cm_mul (cm_mul (contDiffAt_const (c := G.wMat (p + s))) (cm_inv (cm_conjT hP) hdet))
        (contDiffAt_const (c := G.wMat (p + s))))
    exact cm_mul contDiffAt_const (cm_mul (cm_mul contDiffAt_const hmu) contDiffAt_const)
  have hΦd : DifferentiableAt ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := hΦ.differentiableAt one_ne_zero

  have hline : HasDerivAt (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ)
      (gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W)) 0 := by
    rw [show (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ) = _ from funext (line_rep hSZ ξ hZ γ W)]
    set Bm := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1
      with hBm
    have h11 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) + t • Bm) Bm 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const Bm).const_add _).congr_deriv (one_smul _ _)
    have h33 : HasDerivAt (fun t : ℝ => G.wMat (p + s) * ((1 + t • Bm)ᴴ)⁻¹ * G.wMat (p + s))
        (-(G.wMat (p + s) * Bmᴴ * G.wMat (p + s))) 0 :=
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (G.wMat (p + s))) (hd_invT Bm))
        (hasDerivAt_const (0 : ℝ) (G.wMat (p + s)))).congr_deriv (by simp)
    have hmu : HasDerivAt (fun t : ℝ => muP k (p + s) ρ (1 + t • Bm)) (dmuP k (p + s) ρ Bm) 0 :=
      hasDerivAt_block_matrix_three (k := k) (ρ := ρ) h11 (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
        (hasDerivAt_const _ (1 : B.Mat k ρ)) (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _) h33
    exact (hd_mul (hasDerivAt_const (0 : ℝ) (gaXi k ρ σ d ξ Z γ))
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)⁻¹) hmu)
        (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)))).congr_deriv (by simp [lamZ, Bm, Matrix.mul_assoc])
  have hfd : fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z W =
      gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have hlin : HasDerivAt (fun t : ℝ => Z + t • W) W 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const W).const_add Z).congr_deriv (one_smul _ _)
    exact (hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)).unique hline

  obtain ⟨U0, H', hU0, hgU0, hcd, hagree⟩ := hH _ hg
  have hH'd : DifferentiableAt ℝ H' (gaXi k ρ σ d ξ Z γ) :=
    (hcd.differentiableOn (by simp)).differentiableAt (hU0.mem_nhds hgU0)
  have hdc : Continuous fun Z' : G.Mat s => G.detM Z' :=
    Continuous.matrix_det (A := fun Z' : G.Mat s => (Matrix.of Z' : Matrix (Fin s) (Fin s) ℂ)) continuous_id
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[𝓝 Z] fun Z' => H' (gaXi k ρ σ d ξ Z' γ) := by
    have h1 : ∀ᶠ Z' in 𝓝 Z, gaXi k ρ σ d ξ Z' γ ∈ U0 := hΦd.continuousAt.preimage_mem_nhds (hU0.mem_nhds hgU0)
    have h2 : ∀ᶠ Z' in 𝓝 Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hagree _ h1 (ga_mem hMem hRad hd ξ h2 hγ)
  have hcomp : fderiv ℝ (fun Z' : G.Mat s => H' (gaXi k ρ σ d ξ Z' γ)) Z =
      (fderiv ℝ H' (gaXi k ρ σ d ξ Z γ)).comp (fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z) :=
    (hH'd.hasFDerivAt.comp Z hΦd.hasFDerivAt).fderiv
  have hR : ∀ i, RdV (dirZ k ρ ξ i) H (gaXi k ρ σ d ξ Z γ) =
      fderiv ℝ H' (gaXi k ρ σ d ξ Z γ) (gaXi k ρ σ d ξ Z γ * dirZ k ρ ξ i) := by
    intro i
    have hX : B.inLie k (p + s + ρ) (dirZ k ρ ξ i) := ((P.directions_in_parabolic k (p + s) ρ ξ.1.2).2 _).1
    exact (P.BetaSesquilinearity.Dx_hasDerivAt (x := (false, dirZ k ρ ξ i)) hX hU0 hgU0 hg hH'd hagree).deriv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hev.fderiv_eq, hcomp, ContinuousLinearMap.comp_apply, hfd, ← sum_dirZ, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hR i, Matrix.mul_smul, map_smul]

end PI.UnitaryGroupMassFormula.UsCost
