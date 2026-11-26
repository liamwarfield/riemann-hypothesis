module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCbData
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsCB

theorem exists_cbData : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (m : ℕ) (c : Fin (m + 1) → ℕ) (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) (t : Fin m → InfinitePlace K → ℝ), (∀ i v, IsUnit (Xc i v).det) → (∀ j v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v ((Kj j).mulVec x) ^ 2 ≤ Real.exp (t j v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) v x ^ 2) → ∃ cb : CBData Xc Kj, ∀ j v, Real.log (cb.sq j v) ≤ t j v := by
  intro K _ _ _ _ m c Xc Kj t hX h
  refine ⟨{
    AA := fun _ => Unit
    Cl := fun _ _ => Unit
    W := fun i _ => EuclideanSpace ℂ (Fin (c i))
    γ := fun _ _ => 1
    Φ := fun i v x _ => WithLp.toLp 2 ((Xc i v)⁻¹.mulVec x)
    ε := fun _ _ _ _ => 1
    T := fun j v _ _ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v))
    hcl := fun _ => 1
    tmax := fun j v => Real.exp (t j v)
    hyp := ⟨hX, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_,
      fun _ _ => (Real.exp_pos _).le, fun _ _ => by simp⟩ }, ?_⟩
  · intro i v x
    rw [Formalism.DivisionValues.fnorm, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    simp
  · intro j v x
    funext q
    simp only [Formalism.DimensionVariation.liftOp, Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
      mul_one, one_smul, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX _ v), Matrix.mul_one]
  · intro j v _ _
    have key := Formalism.BasicNotions.opNormAt_sq_le (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (hX _) v (IsTotallyComplex.isComplex v)
      (Matrix.mulVecLin (Kj j)) (Real.exp (t j v)) (Real.exp_pos _).le (fun x => by
        rw [← Formalism.BasicNotions.normAt_sq_eq_majAt, ← Formalism.BasicNotions.normAt_sq_eq_majAt]
        exact h j v x)
    have hm : LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
        (Matrix.mulVecLin (Kj j)) = Kj j := by
      ext a b
      simp [LinearMap.toMatrix_apply]
    have e : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((Xc j.succ v)⁻¹ *
          (LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
            (Matrix.mulVecLin (Kj j))).map v.embedding * Xc j.castSucc v))‖ := rfl
    rw [e, hm] at key
    exact key
  · intro j v
    show Real.log (Formalism.DimensionVariation.cbSq (Fintype.card Unit) (Fintype.card Unit) 1 1 (Real.exp (t j v))) ≤ t j v
    simp [Formalism.DimensionVariation.cbSq]

end GlobalTheory.DefRowsCB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBound
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem pairing_eq {K : Type} [Field K] (c n : ℕ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K))
    (y : Fin c → K) (F : Fin n → K) :
    g y F = F ⬝ᵥ (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g *ᵥ y) := by
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g y
  rw [show (Pi.basisFun K (Fin c)).repr y = y from rfl] at h
  rw [h]
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr F]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, Basis.dualBasis_repr]

theorem continuous_cnorm {ι : Type} [Fintype ι] : Continuous (Formalism.HermitianLatticesTheory.cnorm : (ι → ℂ) → ℝ) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  fun_prop

theorem cnorm_nonneg {ι : Type} [Fintype ι] (u : ι → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u := Real.sqrt_nonneg _

theorem bilin_bound {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ)
    (X : Matrix (Fin c) (Fin c) ℂ) (X0 : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin c) ℂ)
    (v : InfinitePlace K) (C : ℝ)
    (h : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => v.embedding (F j)) ⬝ᵥ (S *ᵥ fun i => v.embedding (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ fun j => v.embedding (F j)) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ fun i => v.embedding (y i)))
    (u : Fin n → ℂ) (z : Fin c → ℂ) :
    ‖u ⬝ᵥ (S *ᵥ z)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ u) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ z) := by
  have hv : v.IsComplex := IsTotallyComplex.isComplex v
  have hd : DenseRange (Prod.map (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)))
      (Pi.map (fun _ : Fin c => (v.embedding : K → ℂ)))) :=
    DenseRange.prodMap (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
      (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
  have key : ∀ p : (Fin n → ℂ) × (Fin c → ℂ),
      ‖p.1 ⬝ᵥ (S *ᵥ p.2)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ p.1) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ p.2) := by
    intro p
    induction p using hd.induction_on with
    | hp =>
      apply isClosed_le
      · exact (Continuous.dotProduct continuous_fst
          (Continuous.matrix_mulVec continuous_const continuous_snd)).norm
      · exact (continuous_const.mul (continuous_cnorm.comp
          (Continuous.matrix_mulVec continuous_const continuous_fst))).mul
          (continuous_cnorm.comp (Continuous.matrix_mulVec continuous_const continuous_snd))
    | ih q => exact h q.2 q.1
  exact key (u, z)

end GlobalTheory.PairingOpNorm

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem opNormAt_pairing_sq_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  intro K _ _ _ _ c n X X0 g v A hX hX0 hb
  set σ : K →+* ℂ := v.embedding with hσ
  set S : Matrix (Fin n) (Fin c) ℂ :=
    (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g).map σ with hS
  set C : ℝ := Real.exp (A / 2) with hC
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hCsq : C ^ 2 = Real.exp A := by rw [hC, sq, ← Real.exp_add]; ring_nf
  have hnorm : ∀ {m : ℕ} (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (x : Fin m → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin m)) Y v x = Formalism.HermitianLatticesTheory.cnorm ((Y v)⁻¹ *ᵥ fun i => σ (x i)) := by
    intro m Y x; rfl
  have hK : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) * Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) := by
    intro y F
    have e1 : (fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i)) = σ (g y F) := by
      rw [pairing_eq, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec σ _ y i).symm
    rw [e1, hσ, InfinitePlace.norm_embedding_eq]
    have h1 := hb y F
    rw [hnorm, hnorm] at h1
    have hpos : 0 ≤ C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) *
        Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) :=
      mul_nonneg (mul_nonneg hC0 (cnorm_nonneg _)) (cnorm_nonneg _)
    refine (pow_le_pow_iff_left₀ (apply_nonneg v _) hpos (by norm_num : (2:ℕ) ≠ 0)).1 ?_
    calc v (g y F) ^ 2 ≤ _ := h1
      _ = _ := by rw [mul_pow, mul_pow, hCsq]; ring
  have hB := bilin_bound c n (X v) (X0 v) S v C hK
  have hinv : (Formalism.HN.dualFrame X0 v)⁻¹ = (X0 v)ᵀ := by
    unfold Formalism.HN.dualFrame
    rw [Matrix.nonsing_inv_nonsing_inv]
    rwa [Matrix.det_transpose]
  unfold Formalism.HN.opNormAt
  rw [hinv]
  suffices hT : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X0 v)ᵀ * S * X v))‖ ≤ C by
    rw [← hCsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hT 2
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun ξ => ?_)
  set M : Matrix (Fin n) (Fin c) ℂ := (X0 v)ᵀ * S * X v with hM
  set w : Fin c → ℂ := WithLp.ofLp ξ with hw
  set m : Fin n → ℂ := M *ᵥ w with hm
  have hTx : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) ξ‖ = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, EuclideanSpace.norm_eq,
      Formalism.HermitianLatticesTheory.cnorm, hm, hw]
  have hξ : ‖ξ‖ = Formalism.HermitianLatticesTheory.cnorm w := by
    simp [EuclideanSpace.norm_eq, Formalism.HermitianLatticesTheory.cnorm, hw]
  rw [hTx, hξ]
  have h1 := hB ((X0 v) *ᵥ star m) ((X v) *ᵥ w)
  have i0 : (X0 v)⁻¹ *ᵥ ((X0 v) *ᵥ star m) = star m := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX0, Matrix.one_mulVec]
  have i1 : (X v)⁻¹ *ᵥ ((X v) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]
  rw [i0, i1] at h1
  have e2 : ((X0 v) *ᵥ star m) ⬝ᵥ (S *ᵥ ((X v) *ᵥ w)) = star m ⬝ᵥ m := by
    rw [hm, hM, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : 0 ≤ ∑ i, ‖m i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcn : Formalism.HermitianLatticesTheory.cnorm m ^ 2 = ∑ i, ‖m i‖ ^ 2 := by
    unfold Formalism.HermitianLatticesTheory.cnorm; rw [Real.sq_sqrt hsum]
  have e3 : ‖star m ⬝ᵥ m‖ = Formalism.HermitianLatticesTheory.cnorm m ^ 2 := by
    rw [hcn]
    have : star m ⬝ᵥ m = ((∑ i, ‖m i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_of_nonneg hsum]
  have e4 : Formalism.HermitianLatticesTheory.cnorm (star m) = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [Formalism.HermitianLatticesTheory.cnorm]
  rw [e2, e3, e4] at h1
  rcases (cnorm_nonneg m).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hC0 (cnorm_nonneg w)
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith [h1]

end GlobalTheory.PairingOpNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBoundStatement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  first | exact @GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | exact GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | (intros; apply GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le <;> assumption)
end
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def bund (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (nF : ℕ → ℕ) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ) : ℕ → Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
  | 0 => ⟨Dc.a u, Dc.Xc u⟩
  | k + 1 => if k + 1 ≤ Q.n then ⟨nF (k + 1), XF (k + 1)⟩ else ⟨nS, XS⟩


omit [NumberField K] [StarRing K] in
theorem normAt_of_eq (p : Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)) (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hp : p = ⟨n, X⟩) (hc : n = p.1) (v : InfinitePlace K) (x : Fin p.1 → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin p.1)) p.2 v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (x ∘ Fin.cast hc) := by
  subst hp
  rfl

omit [NumberField K] [StarRing K] in
theorem unit_of_eq (p : Σ n : ℕ, (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)) (n : ℕ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hp : p = ⟨n, X⟩) (v : InfinitePlace K) (hX : IsUnit (X v).det) :
    IsUnit (p.2 v).det := by
  subst hp
  exact hX

section

variable (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem bund_succ_le (k : ℕ) (h : k + 1 ≤ Q.n) : bund Dc u Q nF XF nS XS (k + 1) = ⟨nF (k + 1), XF (k + 1)⟩ := by
  simp [bund, h]

theorem bund_succ_gt (k : ℕ) (h : ¬ k + 1 ≤ Q.n) : bund Dc u Q nF XF nS XS (k + 1) = ⟨nS, XS⟩ := by
  simp [bund, h]

def eN (k : ℕ) (h : k + 1 ≤ Q.n) : (Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) ≃ₗ[K] (Q.F (k + 1)).Forms :=
  (LinearEquiv.funCongrLeft K K (finCongr (congrArg Sigma.fst (bund_succ_le Dc u Q nF XF nS XS k h)).symm)).trans (eF (k + 1))

def eL (k : ℕ) (h : ¬ k + 1 ≤ Q.n) : (Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) ≃ₗ[K] Q.S₁.EqFun :=
  (LinearEquiv.funCongrLeft K K (finCongr (congrArg Sigma.fst (bund_succ_gt Dc u Q nF XF nS XS k h)).symm)).trans eS

def coFN : ∀ i, i ≤ Q.n → (Fin (bund Dc u Q nF XF nS XS i).1 → K) →ₗ[K] (Q.F i).Forms
  | 0, _ => f0
  | k + 1, h => (eN Dc u Q nF eF XF nS XS k h).toLinearMap

def KjN : ∀ j : Fin (Q.n + 1), Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K :=
  Fin.lastCases (motive := fun j : Fin (Q.n + 1) =>
      Matrix (Fin (bund Dc u Q nF XF nS XS (j.val + 1)).1) (Fin (bund Dc u Q nF XF nS XS j.val).1) K)
    (LinearMap.toMatrix' ((eL Dc u Q nF XF nS eS XS Q.n (by omega)).symm.toLinearMap ∘ₗ Q.cpl ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS Q.n le_rfl))
    (fun i => LinearMap.toMatrix' ((eN Dc u Q nF eF XF nS XS i.val i.isLt).symm.toLinearMap ∘ₗ Q.step i.val ∘ₗ
      coFN Dc u Q f0 nF eF XF nS XS i.val i.isLt.le))

end

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
  (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem kerF_N (j : ℕ) (h : j < Q.n) (x : Fin (bund Dc u Q nF XF nS XS j).1 → K) :
    coFN Dc u Q f0 nF eF XF nS XS (j + 1) h ((KjN Dc u Q f0 nF eF XF nS eS XS ⟨j, by omega⟩).mulVec x) =
      Q.step j (coFN Dc u Q f0 nF eF XF nS XS j h.le x) := by
  show coFN Dc u Q f0 nF eF XF nS XS (j + 1) h ((KjN Dc u Q f0 nF eF XF nS eS XS (Fin.castSucc ⟨j, h⟩)).mulVec x) = _
  rw [KjN, Fin.lastCases_castSucc, LinearMap.toMatrix'_mulVec]
  simp [coFN]

theorem kerC_N (x : Fin (bund Dc u Q nF XF nS XS Q.n).1 → K) :
    eL Dc u Q nF XF nS eS XS Q.n (by omega) ((KjN Dc u Q f0 nF eF XF nS eS XS ⟨Q.n, by omega⟩).mulVec x) =
      Q.cpl (coFN Dc u Q f0 nF eF XF nS XS Q.n le_rfl x) := by
  show eL Dc u Q nF XF nS eS XS Q.n (by omega) ((KjN Dc u Q f0 nF eF XF nS eS XS (Fin.last Q.n)).mulVec x) = _
  rw [KjN, Fin.lastCases_last, LinearMap.toMatrix'_mulVec]
  simp

omit [NumberField K] [StarRing K] in
theorem chainMat_zero {m : ℕ} {c : Fin (m + 1) → ℕ} (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) :
    Formalism.DivisionValues.chainMat Kj 0 = 1 := by
  simp [Formalism.DivisionValues.chainMat]

omit [NumberField K] [StarRing K] in
theorem chainMat_succ {m : ℕ} {c : Fin (m + 1) → ℕ} (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (j : Fin m) : Formalism.DivisionValues.chainMat Kj j.succ = Kj j * Formalism.DivisionValues.chainMat Kj j.castSucc := by
  simp [Formalism.DivisionValues.chainMat, Fin.induction_succ]

abbrev cF : Fin (Q.n + 2) → ℕ := fun j => (bund Dc u Q nF XF nS XS j.val).1

theorem chain_le_N : ∀ i (h : i ≤ Q.n) (x : Fin (cF Dc u Q nF XF nS XS 0) → K),
    coFN Dc u Q f0 nF eF XF nS XS i h
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) ⟨i, by omega⟩).mulVec x) = Q.kk.colTo Q.hF i (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x)
  | 0, h, x => by
    show coFN Dc u Q f0 nF eF XF nS XS 0 h ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) 0).mulVec x) = coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x
    rw [chainMat_zero, Matrix.one_mulVec]
  | i + 1, h, x => by
    have hi : i < Q.n + 1 := by omega
    have ih := chain_le_N i (by omega) x
    show coFN Dc u Q f0 nF eF XF nS XS (i + 1) h ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.succ ⟨i, hi⟩)).mulVec x) = Q.step i (Q.kk.colTo Q.hF i (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x))
    rw [chainMat_succ, ← Matrix.mulVec_mulVec, ← ih]
    exact kerF_N Dc u Q f0 nF eF XF nS eS XS i h _

theorem chain_N (x : Fin (cF Dc u Q nF XF nS XS 0) → K) :
    eL Dc u Q nF XF nS eS XS Q.n (by omega)
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.last (Q.n + 1))).mulVec x) = Q.col (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x) := by
  have hi : Q.n < Q.n + 1 := by omega
  show eL Dc u Q nF XF nS eS XS Q.n (by omega)
      ((Formalism.DivisionValues.chainMat (c := cF Dc u Q nF XF nS XS)
        (KjN Dc u Q f0 nF eF XF nS eS XS) (Fin.succ ⟨Q.n, hi⟩)).mulVec x) = Q.cpl (Q.kk.colTo Q.hF Q.n (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) x))
  rw [chainMat_succ, ← Matrix.mulVec_mulVec, ← chain_le_N Dc u Q f0 nF eF XF nS eS XS Q.n le_rfl x]
  exact kerC_N Dc u Q f0 nF eF XF nS eS XS _

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
  (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
  (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
  (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)

theorem unit_N (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det) :
    ∀ k v, IsUnit ((bund Dc u Q nF XF nS XS k).2 v).det
  | 0, v => h1 v
  | k + 1, v => by
    by_cases h : k + 1 ≤ Q.n
    · exact unit_of_eq _ _ _ (bund_succ_le Dc u Q nF XF nS XS k h) v (hXu _ v)
    · exact unit_of_eq _ _ _ (bund_succ_gt Dc u Q nF XF nS XS k h) v (hSu v)

theorem metF_N (h2 : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x))
    (hXi : ∀ i v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (nF i))) (XF i) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (eF i x) (eF i x)) :
    ∀ i (h : i ≤ Q.n) (v : InfinitePlace K) (x : Fin (bund Dc u Q nF XF nS XS i).1 → K),
      ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (bund Dc u Q nF XF nS XS i).1)) (bund Dc u Q nF XF nS XS i).2 v x ^ 2 : ℝ) : ℂ) =
        famIpAt (Q.F i) (Q.hF i) v (coFN Dc u Q f0 nF eF XF nS XS i h x) (coFN Dc u Q f0 nF eF XF nS XS i h x)
  | 0, _, v, x => h2 v x
  | k + 1, h, v, x => by
    rw [normAt_of_eq _ _ _ (bund_succ_le Dc u Q nF XF nS XS k h) (congrArg Sigma.fst (bund_succ_le Dc u Q nF XF nS XS k h)).symm]
    exact hXi (k + 1) v _

theorem metL_N (hSi : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin nS)) XS v x ^ 2 : ℝ) : ℂ) = Q.S₁.ipAt Q.hS₁ v (eS x) (eS x))
    (k : ℕ) (h : ¬ k + 1 ≤ Q.n) (v : InfinitePlace K) (x : Fin (bund Dc u Q nF XF nS XS (k + 1)).1 → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (bund Dc u Q nF XF nS XS (k + 1)).1)) (bund Dc u Q nF XF nS XS (k + 1)).2 v x ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (eL Dc u Q nF XF nS eS XS k h x) (eL Dc u Q nF XF nS eS XS k h x) := by
  rw [normAt_of_eq _ _ _ (bund_succ_gt Dc u Q nF XF nS XS k h) (congrArg Sigma.fst (bund_succ_gt Dc u Q nF XF nS XS k h)).symm]
  exact hSi v _

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def chainOf (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (no : Bs.J → ℕ)
    (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)
    (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det)
    (h5 : ∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) : ColChain Dc u where
  mm := Q.n + 1
  lf l := ⟨min (no l) Q.n, by omega⟩
  c := cF Dc u Q nF XF nS XS
  c0 := rfl
  X i := (bund Dc u Q nF XF nS XS i.val).2
  X_unit i v := unit_N Dc u Q nF XF nS XS h1 hXu hSu i.val v
  X_zero _ _ _ := rfl
  Kj := KjN Dc u Q f0 nF eF XF nS eS XS
  PtL := g ∘ₗ (eL Dc u Q nF XF nS eS XS Q.n (by omega)).toLinearMap
  fact φ F := by
    rw [h5]
    show g (Q.col (coFN Dc u Q f0 nF eF XF nS XS 0 (Nat.zero_le _) φ)) F = _
    rw [← chain_N Dc u Q f0 nF eF XF nS eS XS φ]
    rfl

def tieOf (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (no : Bs.J → ℕ)
    (nF : ℕ → ℕ) (eF : ∀ i, (Fin (nF i) → K) ≃ₗ[K] (Q.F i).Forms) (XF : ∀ i, InfinitePlace K → Matrix (Fin (nF i)) (Fin (nF i)) ℂ)
    (nS : ℕ) (eS : (Fin nS → K) ≃ₗ[K] Q.S₁.EqFun) (XS : InfinitePlace K → Matrix (Fin nS) (Fin nS) ℂ)
    (h1 : ∀ v, IsUnit (Dc.Xc u v).det) (hXu : ∀ i v, IsUnit (XF i v).det) (hSu : ∀ v, IsUnit (XS v).det)
    (h5 : ∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F)
    (h2 : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x))
    (hXi : ∀ i v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (nF i))) (XF i) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (eF i x) (eF i x))
    (hSi : ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin nS)) XS v x ^ 2 : ℝ) : ℂ) = Q.S₁.ipAt Q.hS₁ v (eS x) (eS x)) :
    ChainTie (chainOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5) Q where
  hmm := rfl
  coF := coFN Dc u Q f0 nF eF XF nS XS
  coL := (eL Dc u Q nF XF nS eS XS Q.n (by omega)).toLinearMap
  metF := metF_N Dc u Q f0 nF eF XF nS XS h2 hXi
  metL := metL_N Dc u Q nF XF nS eS XS hSi Q.n (by omega)
  kerF := kerF_N Dc u Q f0 nF eF XF nS eS XS
  kerC := kerC_N Dc u Q f0 nF eF XF nS eS XS

end GlobalTheory.DefRowsChain

namespace GlobalTheory.DefRowsChain

theorem sq_le_of (a b s : ℝ) (za zb : ℂ) (ha : ((a ^ 2 : ℝ) : ℂ) = za) (hb : ((b ^ 2 : ℝ) : ℂ) = zb)
    (hs : za.re ≤ Real.exp s * zb.re) : a ^ 2 ≤ Real.exp s * b ^ 2 := by
  subst ha hb
  rw [Complex.ofReal_re, Complex.ofReal_re] at hs
  exact hs

def tOf {K : Type} [Field K] [NumberField K] [StarRing K] {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] {R : RecNums J Pl}
    (hn : HtNums R (InfinitePlace K)) (n : ℕ) (no : J → ℕ) (j : Fin (n + 1)) (v : InfinitePlace K) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => (⟨min (no l) n, by omega⟩ : Fin (n + 1)) = j), hn.sz l v

theorem rowsBody_of_framed : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (hn : HtNums R (InfinitePlace K)) (no : Bs.J → ℕ) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ), (∀ v, IsUnit (Dc.Xc u v).det) → (∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) = famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x)) → (∀ i, FamFramed (Q.F i) (Q.hF i)) → DatFramed Q.S₁ Q.hS₁ → (∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) → IsFrames Df X0 → FactorBounds Q no hn.sz → (∀ (v : InfinitePlace K) (ψ : Q.S₁.EqFun) F, v (g ψ F) ^ 2 ≤ Real.exp hn.hPn * (Q.S₁.ipAt Q.hS₁ v ψ ψ).re * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody Dc u Q f0 R := by
  intro K _ _ _ _ Bs Df Dc u Q f0 g Pl _ _ R hn no X0 h1 h2 h3 h4 h5 h6 h7 h8
  choose nF eF XF hXu hXi using h3
  obtain ⟨nS, eS, XS, hSu, hSi⟩ := h4
  let ch := chainOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5
  let T := tieOf Dc u Q f0 g no nF eF XF nS eS XS h1 hXu hSu h5 h2 hXi hSi
  have hb : ∀ (j : Fin (Q.n + 1)) v (x : Fin (ch.c j.castSucc) → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v ((ch.Kj j).mulVec x) ^ 2 ≤
        Real.exp (tOf hn Q.n no j v) *
          Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc) v x ^ 2 := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      intro v x
      have hs : tOf hn Q.n no (Fin.last Q.n) v = ∑ l ∈ Finset.univ.filter (fun l => Q.n ≤ no l), hn.sz l v := by
        refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
        simp only [Fin.ext_iff, Fin.val_last]
        omega
      rw [hs]
      refine sq_le_of _ _ _ _ _ (T.cpl_norm v x) (T.metF Q.n le_rfl v x) ?_
      exact h7.2 v _
    | cast i =>
      intro v x
      have hs : tOf hn Q.n no (Fin.castSucc i) v = ∑ l ∈ Finset.univ.filter (fun l => no l = i.val), hn.sz l v := by
        refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
        simp only [Fin.ext_iff, Fin.val_castSucc]
        have := i.isLt
        omega
      rw [hs]
      refine sq_le_of _ _ _ _ _ (T.step_norm i.val i.isLt v x) (T.metF i.val i.isLt.le v x) ?_
      exact h7.1 i.val i.isLt v _
  obtain ⟨cb, hcb⟩ := GlobalTheory.DefRowsCB.exists_cbData K (Q.n + 1) ch.c ch.X ch.Kj
    (tOf hn Q.n no) ch.X_unit hb
  refine ⟨ch, T, fun _ => rfl, X0, h6, hn, fun v => ?_, cb, hcb⟩
  refine GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound K _ _ (ch.X (Fin.last ch.mm)) X0 ch.PtL v hn.hPn (ch.X_unit _ v) (h6 v).1 fun y F => ?_
  have hm := T.metL v y
  have e : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) v y ^ 2 =
      (Q.S₁.ipAt Q.hS₁ v (T.coL y) (T.coL y)).re := by
    have := congrArg Complex.re hm
    rw [Complex.ofReal_re] at this
    exact this
  rw [e]
  exact h8 v (T.coL y) F

end GlobalTheory.DefRowsChain
