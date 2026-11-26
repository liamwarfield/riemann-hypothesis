module

public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.HookProducts.RBTieFrame
open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Vec

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem vecAt_map (b : Basis ι K V) (b' : Basis κ K W) (v : InfinitePlace K) (u : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.vecAt b' v (u x) = (LinearMap.toMatrix b b' u).map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.HermitianLatticesTheory.vecAt, ← LinearMap.toMatrix_mulVec_repr b b' u x, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul]

theorem vecAt_std {d : ℕ} (v : InfinitePlace K) (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v x = fun l => v.embedding (x l) := by
  funext l
  simp [Formalism.HermitianLatticesTheory.vecAt]

end Vec

theorem sum_star_mulVec_single {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (i j : n) :
    ∑ k, star ((C *ᵥ Pi.single i 1) k) * (C *ᵥ Pi.single j 1) k = (Cᴴ * C) i j := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

section Comparison₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

def cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (LinearMap.toMatrix (Pi.basisFun K (Fin d)) b e.toLinearMap).map v.embedding

def cQ (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (LinearMap.toMatrix b (Pi.basisFun K (Fin d)) e.symm.toLinearMap).map v.embedding

theorem basisChange_mul_basisChangeInv (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cP b e v * cQ b e v = 1 := by
  unfold cP cQ
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
  simp

theorem cQ_mul_cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cQ b e v * cP b e v = 1 := by
  unfold cP cQ
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
  simp

theorem fcoord_e (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
    (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord b XA v (e y) = ((XA v)⁻¹ * cP b e v) *ᵥ (fun l => v.embedding (y l)) := by
  show (XA v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt b v (e y) = _
  rw [← Matrix.mulVec_mulVec]
  congr 1
  rw [show e y = e.toLinearMap y from rfl, vecAt_map (Pi.basisFun K (Fin d)) b v e.toLinearMap y, vecAt_std]
  rfl

theorem fcoord_std (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v y = (X v)⁻¹ *ᵥ (fun l => v.embedding (y l)) := by
  show (X v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v y = _
  rw [vecAt_std]

theorem emb_single (v : InfinitePlace K) (k : Fin d) :
    (fun l => v.embedding ((Pi.single k (1 : K) : Fin d → K) l)) = Pi.single k (1 : ℂ) := by
  funext l
  by_cases h : l = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_tie (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V)
    (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (v : InfinitePlace K) :
    ((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  ext k l
  have h1 := h v (Pi.single k (1 : K) : Fin d → K) (Pi.single l (1 : K) : Fin d → K)
  unfold Formalism.HermitianLatticesTheory.majAt at h1
  rw [fcoord_e, fcoord_e, fcoord_std, fcoord_std, emb_single, emb_single] at h1
  rw [← sum_star_mulVec_single, ← sum_star_mulVec_single]
  exact h1

def cU (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix ι (Fin d) ℂ :=
  (XA v)⁻¹ * cP b e v * X v

def cV (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : Matrix (Fin d) ι ℂ :=
  (X v)⁻¹ * cQ b e v * XA v

variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)

theorem cU_conj_mul (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ * cU b XA X e v = 1 := by
  have hg := gram_tie b XA X e h v
  have hinv : (X v)⁻¹ * X v = 1 := Matrix.nonsing_inv_mul _ hX
  calc (cU b XA X e v)ᴴ * cU b XA X e v
      = (X v)ᴴ * (((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v)) * X v := by
        simp only [cU, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (X v)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) * X v := by rw [hg]
    _ = ((X v)⁻¹ * X v)ᴴ * ((X v)⁻¹ * X v) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hinv, Matrix.conjTranspose_one, Matrix.mul_one]

theorem cU_mul_cV (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * cV b XA X e v = 1 := by
  calc cU b XA X e v * cV b XA X e v
      = (XA v)⁻¹ * (cP b e v * (X v * (X v)⁻¹) * cQ b e v) * XA v := by
        simp only [cU, cV, Matrix.mul_assoc]
    _ = (XA v)⁻¹ * XA v := by
        rw [Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, basisChange_mul_basisChangeInv, Matrix.mul_one]
    _ = 1 := Matrix.nonsing_inv_mul _ hXA

theorem cU_conj_eq (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : (cU b XA X e v)ᴴ = cV b XA X e v := by
  calc (cU b XA X e v)ᴴ = (cU b XA X e v)ᴴ * (cU b XA X e v * cV b XA X e v) := by
        rw [cU_mul_cV b XA X e v hXA hX, Matrix.mul_one]
    _ = ((cU b XA X e v)ᴴ * cU b XA X e v) * cV b XA X e v := (Matrix.mul_assoc _ _ _).symm
    _ = cV b XA X e v := by rw [cU_conj_mul b XA X e v h hX, Matrix.one_mul]

theorem cU_mul_conj (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * (cU b XA X e v)ᴴ = 1 := by
  rw [cU_conj_eq b XA X e v h hXA hX, cU_mul_cV b XA X e v hXA hX]

theorem basisChange_mul_X (hXA : IsUnit (XA v).det) : cP b e v * X v = XA v * cU b XA X e v := by
  unfold cU
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul]

theorem cQ_mul_XA (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cQ b e v * XA v = X v * (cU b XA X e v)ᴴ := by
  rw [cU_conj_eq b XA X e v h hXA hX]
  unfold cV
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul]

theorem frame_unit_of_tie (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) : IsUnit (X v).det := by
  by_contra hX
  have hinv : (X v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hX
  have hg := gram_tie b XA X e h v
  rw [hinv, Matrix.conjTranspose_zero, Matrix.zero_mul] at hg
  have hM : (XA v)⁻¹ * cP b e v = 0 := by
    open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.mp hg
  have hP : cP b e v = 0 := by
    have h2 := congrArg (fun M => XA v * M) hM
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul, Matrix.mul_zero] at h2
    exact h2
  have h1 := cQ_mul_cP b e v
  rw [hP, Matrix.mul_zero] at h1
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · exact hX (by simp)
  · have h3 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h3

end Comparison₂

section Norm

end Norm

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {VN VR : Type} [AddCommGroup VN] [Module K VN] [AddCommGroup VR] [Module K VR]
  {ιN ιR : Type} [Fintype ιN] [DecidableEq ιN] [Fintype ιR] [DecidableEq ιR] {d n : ℕ}

theorem dualFrame_inv {ι : Type} [Fintype ι] [DecidableEq ι] (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) : (Formalism.HN.dualFrame X v)⁻¹ = (X v)ᵀ := by
  show ((X v)ᵀ)⁻¹⁻¹ = (X v)ᵀ
  exact Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hX)

theorem transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : (Uᵀ)ᴴ * Uᵀ = (U * Uᴴ)ᵀ := by
  rw [Matrix.transpose_mul]
  rfl

theorem conjT_transpose_isom {ι κ : Type} [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ) : ((Uᴴ)ᵀ)ᴴ * (Uᴴ)ᵀ = (Uᴴ * U)ᵀ := by
  rw [Matrix.transpose_mul]
  congr 1
  ext i j
  simp

private theorem toMatrix_eq_transpose_mul_mul_of_comp (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B =
      (LinearMap.toMatrix (Pi.basisFun K (Fin n)) bR eR.toLinearMap)ᵀ *
        LinearMap.toMatrix bN bR.dualBasis Bk *
          LinearMap.toMatrix (Pi.basisFun K (Fin d)) bN eN.toLinearMap := by
  ext a b
  simp only [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.mul_apply, Matrix.transpose_apply,
    LinearEquiv.coe_coe, Finset.sum_mul]
  rw [← hB]
  conv_lhs => rw [← bN.sum_repr (eN (Pi.basisFun K (Fin d) b)), ← bR.sum_repr (eR (Pi.basisFun K (Fin n) a))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem toMatrix_map_embedding_eq_cP_mul (bN : Basis ιN K VN) (bR : Basis ιR K VR) (eN : (Fin d → K) ≃ₗ[K] VN)
    (eR : (Fin n → K) ≃ₗ[K] VR) (Bk : VN →ₗ[K] Module.Dual K VR)
    (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K)) (hB : ∀ x y, Bk (eN x) (eR y) = B x y)
    (v : InfinitePlace K) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding =
      (cP bR eR v)ᵀ * (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * cP bN eN v := by
  rw [toMatrix_eq_transpose_mul_mul_of_comp bN bR eN eR Bk B hB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rfl

private theorem opNorm_toEuclideanLin_mul_le {l m o : Type} [Fintype l] [Fintype m] [Fintype o] [DecidableEq l]
    [DecidableEq m] [DecidableEq o] (A : Matrix l m ℂ) (B : Matrix m o ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B))‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ := by
  have h := Matrix.l2_opNorm_mul A B
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using h

private theorem opNorm_toEuclideanLin_le_one_of_isometry {l m : Type} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (W : Matrix l m ℂ) (hW : Wᴴ * W = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W)‖ ≤ 1 := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self W
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix m m ℂ)
  rw [hW] at h1
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at h2
  simp only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] at h1 h2
  have hs := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin W))
  have ht := norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ)))
  have ht1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix m m ℂ))‖ ≤ 1 := by
    nlinarith
  nlinarith

private theorem opNorm_toEuclideanLin_unitary_mul_mul_eq {a b c e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq e]
    (M : Matrix a b ℂ) (L : Matrix c a ℂ) (R : Matrix b e ℂ) (L' : Matrix a c ℂ) (R' : Matrix e b ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hL' : L'ᴴ * L' = 1) (hR' : R'ᴴ * R' = 1)
    (hLL : L' * L = 1) (hRR : R * R' = 1) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖ =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ := by
  apply le_antisymm
  · calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR
      _ = _ := by ring
  · have hM : M = L' * (L * M * R) * R' := by
      calc M = (L' * L) * M * (R * R') := by rw [hLL, hRR, Matrix.one_mul, Matrix.mul_one]
        _ = L' * (L * M * R) * R' := by simp only [Matrix.mul_assoc]
    conv_lhs => rw [hM]
    calc _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L' * (L * M * R)))‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L')‖ *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R')‖ := by
          gcongr; exact opNorm_toEuclideanLin_mul_le _ _
      _ ≤ (1 * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L * M * R))‖) * 1 := by
          gcongr
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hL'
          · exact opNorm_toEuclideanLin_le_one_of_isometry _ hR'
      _ = _ := by ring

theorem opNormAt_tie (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) (v : InfinitePlace K) :
    Formalism.HN.opNormAt bN XN bR.dualBasis (Formalism.HN.dualFrame XR) v Bk =
      Formalism.HN.opNormAt (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v B := by
  have key : (Formalism.HN.dualFrame XE v)⁻¹ *
        (LinearMap.toMatrix (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin n)).dualBasis B).map v.embedding *
          Xc v =
      (cU bR XR XE eR v)ᵀ * ((Formalism.HN.dualFrame XR v)⁻¹ *
        (LinearMap.toMatrix bN bR.dualBasis Bk).map v.embedding * XN v) * cU bN XN Xc eN v := by
    have h1 := basisChange_mul_X (b := bR) (e := eR) (X := XE) (XA := XR) (v := v) (hXR v)
    have h2 := basisChange_mul_X (b := bN) (e := eN) (X := Xc) (XA := XN) (v := v) (hXN v)
    rw [dualFrame_inv XE v (hXE v), dualFrame_inv XR v (hXR v), toMatrix_map_embedding_eq_cP_mul bN bR eN eR Bk B hB v]
    simp only [Matrix.mul_assoc]
    rw [h2, ← Matrix.mul_assoc (XE v)ᵀ, ← Matrix.transpose_mul, h1, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  unfold Formalism.HN.opNormAt
  rw [key]
  symm
  refine opNorm_toEuclideanLin_unitary_mul_mul_eq _ _ _ ((cU bR XR XE eR v)ᴴ)ᵀ (cU bN XN Xc eN v)ᴴ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [transpose_isom, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_conj_mul (h := hN) (hX := hXc v)
  · rw [conjT_transpose_isom, cU_conj_mul (h := hR) (hX := hXE v), Matrix.transpose_one]
  · rw [Matrix.conjTranspose_conjTranspose]
    exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)
  · rw [← Matrix.transpose_mul, cU_mul_conj (h := hR) (hXA := hXR v) (hX := hXE v), Matrix.transpose_one]
  · exact cU_mul_conj (h := hN) (hXA := hXN v) (hX := hXc v)

theorem htMap_tie (bN : Basis ιN K VN) (XN : InfinitePlace K → Matrix ιN ιN ℂ) (bR : Basis ιR K VR)
    (XR : InfinitePlace K → Matrix ιR ιR ℂ) (Xc : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (eN : (Fin d → K) ≃ₗ[K] VN) (eR : (Fin n → K) ≃ₗ[K] VR)
    (hN : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bN XN v (eN x) (eN y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) Xc v x y)
    (hR : ∀ v x y, Formalism.HermitianLatticesTheory.majAt bR XR v (eR x) (eR y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXN : ∀ v, IsUnit (XN v).det) (hXR : ∀ v, IsUnit (XR v).det) (hXc : ∀ v, IsUnit (Xc v).det)
    (hXE : ∀ v, IsUnit (XE v).det)
    (Bk : VN →ₗ[K] Module.Dual K VR) (B : (Fin d → K) →ₗ[K] Module.Dual K (Fin n → K))
    (hB : ∀ x y, Bk (eN x) (eR y) = B x y) :
    Formalism.HN.htMap bN XN bR.dualBasis (Formalism.HN.dualFrame XR) Bk =
      Formalism.HN.htMap (Pi.basisFun K (Fin d)) Xc (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) B := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [opNormAt_tie bN XN bR XR Xc XE eN eR hN hR hXN hXR hXc hXE Bk B hB v]

end Op

end Formalism.MainNotions.DIV.HookProducts.RBTie
