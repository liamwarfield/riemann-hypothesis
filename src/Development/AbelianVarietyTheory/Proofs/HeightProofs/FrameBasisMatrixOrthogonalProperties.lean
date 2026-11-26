module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockBasisMatrix

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_basis (S : HSpace E) (Q : Matrix (Fin S.rank) (Fin S.rank) E) (hQ : IsUnit Q.det) :
    ∃ b : Module.Basis (Fin S.rank) E S.V, Q = S.frame.toMatrix b := by
  refine ⟨S.frame.map (Matrix.toLinearEquiv S.frame Q hQ), ?_⟩
  ext i j
  simp [Module.Basis.toMatrix_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Finsupp.single_apply]

theorem isUnit_det (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) : IsUnit (S.frame.toMatrix b).det := by
  letI := Module.Basis.invertibleToMatrix S.frame b
  exact Matrix.isUnit_det_of_invertible _

theorem gram_change (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i j : Fin S.rank) :
    (((S.frame.toMatrix b).map star)ᵀ * S.gram * S.frame.toMatrix b) i j = S.hT (b i) (b j) := by
  conv_rhs => rw [← S.frame.sum_repr (b i), ← S.frame.sum_repr (b j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram,
    map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem diag_ne_zero (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (i : Fin S.rank) : S.hT (b i) (b i) ≠ 0 := by
  intro h0
  refine b.ne_zero i (S.nondeg.2 _ fun x => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  by_cases hk : k = i
  · rw [hk, h0, smul_zero]
  · rw [ho k i hk, smul_zero]

theorem diag_real (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) (x : S.V) :
    (((τ (S.hT x x)).re : ℝ) : ℂ) = τ (S.hT x x) := by
  rw [← Complex.conj_eq_iff_re, ← hτ]
  exact congrArg τ (S.herm.eq x x)

theorem toMatrix_mul_diag (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (s : Module.End E S.V)
    (c : Fin S.rank → E) (hs : ∀ i, s (b i) = c i • b i) :
    LinearMap.toMatrix S.frame S.frame s * S.frame.toMatrix b = S.frame.toMatrix b * Matrix.diagonal c := by
  rw [linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [Matrix.mul_diagonal, LinearMap.toMatrix_apply, hs, Module.Basis.toMatrix_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

theorem orthogonal_basis (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) :
    (∀ i, (τ (S.hT (b i) (b i))).re ≠ 0) ∧
    ((S.frame.toMatrix b).map τ)ᴴ * S.gram.map τ * (S.frame.toMatrix b).map τ =
      Matrix.diagonal (fun i => (((τ (S.hT (b i) (b i))).re : ℝ) : ℂ)) ∧
    ∀ s : Module.End E S.V, (∀ i, s (b i) = if 0 < (τ (S.hT (b i) (b i))).re then b i else -b i) →
      (LinearMap.toMatrix S.frame S.frame s).map τ * (S.frame.toMatrix b).map τ =
        (S.frame.toMatrix b).map τ * Matrix.diagonal (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : ℂ) else -1) := by
  refine ⟨fun i h => ?_, ?_, fun s hs => ?_⟩
  · have := diag_real S τ hτ (b i)
    rw [h, Complex.ofReal_zero] at this
    exact diag_ne_zero S b ho i ((map_eq_zero τ).1 this.symm)
  · have e : ((S.frame.toMatrix b).map τ)ᴴ = (((S.frame.toMatrix b).map star)ᵀ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, hτ]
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    rw [Matrix.map_apply, gram_change]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, diag_real S τ hτ]
    · rw [Matrix.diagonal_apply_ne _ hij, ho i j hij, map_zero]
  · have h := toMatrix_mul_diag S b s (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : E) else -1)
      (fun i => by rw [hs i]; split_ifs <;> simp)
    rw [← Matrix.map_mul, h, Matrix.map_mul, Matrix.diagonal_map (map_zero τ)]
    congr 2
    funext i
    split_ifs <;> simp

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem basis_matrix : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  intro D V
  exact ⟨exists_basis V, fun b => ⟨isUnit_det V b, gram_change V b,
    fun ho τ => orthogonal_basis V b ho (tauE D τ) (tauE_star τ)⟩⟩

end GlobalTheory.FockBasisMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_basis_matrix_orthogonal_properties : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  first | exact @GlobalTheory.FockBasisMatrix.basis_matrix | exact GlobalTheory.FockBasisMatrix.basis_matrix | (intros; apply GlobalTheory.FockBasisMatrix.basis_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePos
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Kronecker

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_kron_pos {m n : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * P i k * Q j l * x k l := by
  have h := (hP.kronecker hQ).dotProduct_mulVec_pos (x := fun p : Fin m × Fin n => x p.1 p.2)
    (fun h0 => hx (by ext i j; exact congrFun h0 (i, j)))
  convert h using 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum, kroneckerMap_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.star_def]; ring

theorem IsCart.adj_mul {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : IsCart G t) :
    (t.map (starRingEnd ℂ))ᵀ * G = G * t := by
  have e : (t.map (starRingEnd ℂ))ᵀ = tᴴ := by ext i j; rfl
  rw [e]
  calc tᴴ * G = tᴴ * G * (t * t) := by rw [h.1, Matrix.mul_one]
    _ = G * t := by rw [← Matrix.mul_assoc, h.2.1]

theorem hC_actC_pos {D : D7} (V W : HSp D) (τ : D.what₂.Tau) (t : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : IsCart (gramAt D V τ) t) (h' : IsCart (gramAt D W τ) t')
    (x : WC V W) (hx : x ≠ 0) : 0 < hC V W τ x (actC V W t t' x) := by
  unfold hC actC
  split_ifs with hr
  · have p := sum_kron_pos h.2.2.transpose h'.2.2 x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_small] at p ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    convert p using 2
    rw [← h.adj_mul]
    simp only [Matrix.mul_assoc]
  · have p := sum_kron_pos h.2.2 h'.2.2.transpose x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_large] at p ⊢
    convert p using 2
    rw [← h'.adj_mul]
    simp only [Matrix.mul_assoc]

theorem symplC_jAt_neg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V)
    (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') →
    ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  intro D V W τ s s' h h' x hx
  have p := hC_actC_pos V W τ _ _ h h' x hx
  have q := xi_zero_im_pos D τ
  unfold symplC jAt
  rw [hC_smul_right]
  obtain ⟨p1, p2⟩ := Complex.pos_iff.1 p
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← p2]
  nlinarith [mul_pos p1 q]

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePosStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  first | exact @GlobalTheory.FockCompare.symplC_jAt_neg | exact GlobalTheory.FockCompare.symplC_jAt_neg | (intros; apply GlobalTheory.FockCompare.symplC_jAt_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariables
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.ThetaPeriod

variable {D : D7}

def mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : AF D.host.F →+ WA V W where
  toFun a := Matrix.of fun i j => a ⊗ₜ[D.host.F] γ i j
  map_zero' := by ext i j; exact TensorProduct.zero_tmul _ _
  map_add' x y := by ext i j; exact TensorProduct.add_tmul _ _ _

theorem continuous_mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    Continuous (mulRat V W γ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun a : AF D.host.F => mulRat V W γ a i j) =
      fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
  rw [e]
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  exact Continuous.smul (M := AF D.host.F) (X := AE D) (f := fun a : AF D.host.F => a) continuous_id continuous_const

theorem mulRat_one (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    mulRat V W γ 1 = ratW V W γ := by
  ext i j; rfl

theorem ratW_nsmul (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (N : ℕ) :
    ratW V W (N • γ) = N • ratW V W γ := by
  ext i j
  exact (incA D).toAddMonoidHom.map_nsmul N (γ i j)

theorem norm_periodic (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hU : ∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) →
      ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U)
    (V W : HSp D) (f : WA V W → ℂ) (hf : IsThetaFun ψ V W f) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨N, hN, hmem⟩ := hU (U.comap (mulRat V W γ)) (hUo.preimage (continuous_mulRat V W γ))
  refine ⟨N, hN, fun w => ?_⟩
  set u : WA V W := mulRat V W γ (pairA D.host.F 0 (N : Af D.host.F)) with hu
  set r : WA V W := mulRat V W γ (pairA D.host.F (N : Ainf D.host.F) 0) with hr
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hr0 : IsRealW V W r := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hsum : r + u = N • ratW V W γ := by
    rw [hr, hu, ← AddMonoidHom.map_add (f := _), ← mulRat_one, ← AddMonoidHom.map_nsmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (N : Ainf D.host.F) + 0 = N • (1 : Ainf D.host.F)
      rw [add_zero, nsmul_one]
    · show 0 + (N : Af D.host.F) = N • (1 : Af D.host.F)
      rw [zero_add, nsmul_one]
  have hpu : piW θ V W u = 0 := by
    funext τ i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu0 i) j
    show θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  have hi : iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)) = r := by
    rw [Nat.cast_smul_eq_nsmul, ← AddMonoidHom.map_nsmul, ← hsum, AddMonoidHom.map_add (f := _), hpu, add_zero,
      h.iota_pi hr0]
  have h1 : ∀ x, ‖f (x + u)‖ = ‖f x‖ := fun x => by
    have := congrFun (hUf u hmem hu0) x
    rw [← this, Heisenberg₂, norm_mul, hψ, one_mul]
  have h2 := congrArg norm (hf.quasi (N • γ) w)
  rw [norm_mul, hψ, one_mul, ratW_nsmul, ← hsum] at h2
  rw [hi, ← h1, ← h2, add_assoc, add_comm]

end GlobalTheory.FockCompare.ThetaPeriod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariablesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaFunction_periodic_real_variables : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → (∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) → ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U) → ∀ (V W : HSp D) (f : WA V W → ℂ), IsThetaFun ψ V W f → ∀ γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  first | exact @GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | exact GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | (intros; apply GlobalTheory.FockCompare.ThetaPeriod.norm_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem eq_zero_of_bounded_of_creation_eq {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : R → ℂ) (hF : Differentiable ℝ F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) (u u' : R) (a b q : ℝ) (hq : 0 < q)
    (h : ∀ s t : ℝ, fderiv ℝ F (s • u - t • u') u - Complex.I * fderiv ℝ F (s • u - t • u') u' =
      Real.pi * Complex.I * ((a + t * q) - Complex.I * (b + s * q)) * F (s • u - t • u')) :
    F 0 = 0 := by
  let L : ℂ →L[ℝ] R := Complex.reCLM.smulRight u - Complex.imCLM.smulRight u'
  have hL : ∀ z : ℂ, L z = z.re • u - z.im • u' := fun z => rfl
  let re' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let im' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hre : ∀ z : ℂ, re' z = (z.re : ℂ) := fun z => rfl
  have him : ∀ z : ℂ, im' z = (z.im : ℂ) := fun z => rfl
  let c1 : ℂ := -(Real.pi * Complex.I)
  let c2 : ℂ := -(Real.pi * q / 2)
  let φ : ℂ → ℂ := fun z => c1 * (a * re' z - b * im' z) + c2 * (re' z * re' z + im' z * im' z)
  let H : ℂ → ℂ := fun z => Complex.exp (φ z) * F (L z)
  have hHd : Differentiable ℂ H := by
    intro z
    have r := re'.hasFDerivAt (x := z)
    have i := im'.hasFDerivAt (x := z)
    have h1 := ((((r.const_mul (a : ℂ)).sub (i.const_mul (b : ℂ))).const_mul c1).add
      (((r.mul r).add (i.mul i)).const_mul c2)).cexp
    have h2 := (hF (L z)).hasFDerivAt.comp z (L.hasFDerivAt (x := z))
    have h3 : HasFDerivAt H _ z := h1.mul h2
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨h3.differentiableAt, ?_⟩
    rw [h3.fderiv]
    have e := h z.re z.im
    rw [← hL] at e
    have e1 : L 1 = u := by simp [hL]
    have eI : L Complex.I = -u' := by simp [hL]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, e1, eI, hre, him, smul_eq_mul, map_neg, Function.comp_apply,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_zero, Complex.ofReal_one]
    generalize Complex.exp _ = E
    rw [sub_eq_iff_eq_add] at e
    rw [e]
    simp only [c1, c2]
    linear_combination (-(E * fderiv ℝ F (L z) u') + E * F (L z) * Real.pi * (-(z.im * q) + Complex.I * (b + z.re * q))) * Complex.I_mul_I
  have hn : ∀ z, ‖H z‖ ≤ C * Real.exp (-(Real.pi * q / 2) * ‖z‖ ^ 2) := by
    intro z
    have : (φ z).re = -(Real.pi * q / 2) * ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [φ, c1, c2, hre, him]
    simp only [H]
    rw [norm_mul, Complex.norm_exp, this, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have ht : Filter.Tendsto H (Filter.cocompact ℂ) (nhds 0) := by
    refine squeeze_zero_norm hn ?_
    have hp : -(Real.pi * q / 2) < 0 := by have := Real.pi_pos; have : 0 < Real.pi * q / 2 := by positivity
                                           linarith
    have t1 : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
    have t2 := (Real.tendsto_exp_atBot.comp (t1.const_mul_atTop_of_neg hp)).const_mul C
    simpa using t2
  have h0 := hHd.apply_eq_of_tendsto_cocompact 0 ht
  simp only [H, map_zero, mul_eq_zero, Complex.exp_ne_zero, false_or] at h0
  exact h0

theorem eq_zero_of_creation_eq_zero : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  intro G R _ _ _ _ ι π om hπ hform hanti f hf hb u u' hq h0
  funext w
  obtain ⟨C, hC⟩ := hb w
  have hF : Differentiable ℝ fun x : R => f (w + ι x) := (hf w).differentiable (by simp)
  have huu : ∀ v, om v v = 0 := fun v => by have := hanti v v; linarith
  have key := eq_zero_of_bounded_of_creation_eq (fun x : R => f (w + ι x)) hF C hC u u'
    (om (π w) u) (om (π w) u') (om u u') hq (fun s t => by
      set x := s • u - t • u' with hx
      have e := congrFun h0 (w + ι x)
      have hfd : fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 = fderiv ℝ (fun y : R => f (w + ι y)) x := by
        have : (fun y : R => f (w + ι x + ι y)) = fun y => (fun y : R => f (w + ι y)) (x + y) := by
          funext y; simp only [map_add (f := _), add_assoc]
        rw [this, fderiv_comp_add_left (f := fun y : R => f (w + ι y)), add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hform f hf, hfd] at e
      have e1 : om (π (w + ι x)) u = om (π w) u + t * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu, hanti u u']
      have e2 : om (π (w + ι x)) u' = om (π w) u' + s * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu]
      rw [e1, e2] at e
      push_cast at e
      linear_combination e)
  simpa using key

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  first | exact @GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | exact GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | (intros; apply GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreation
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreation
noncomputable section

namespace GlobalTheory.FockCompare.WeylInduct

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M]

theorem killed_zero (a : I → Module.End ℂ M) (m : M) : Killed a 0 m ↔ m = 0 := by
  constructor
  · intro h; exact h [] rfl
  · intro h l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact h

theorem killed_succ (a : I → Module.End ℂ M) (N : ℕ) (m : M) :
    Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    obtain rfl | ⟨l', i, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

noncomputable def prodE (E : Module.End ℂ M) (lam : ℂ) : ℕ → ℕ → M → M
  | 0, _, x => x
  | N + 1, j, x => prodE E lam N (j + 1) (E x - ((j : ℂ) * lam) • x)

theorem prodE_comm (E : Module.End ℂ M) (lam : ℂ) (N : ℕ) :
    ∀ (j : ℕ) (x : M), prodE E lam N j (E x) = E (prodE E lam N j x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [← ih, map_sub, map_smul]

theorem shift_prodE (E A : Module.End ℂ M) (lam : ℂ) (h : ∀ x, A (E x) = E (A x) + lam • A x) (N : ℕ) :
    ∀ (j : ℕ) (x : M), A (prodE E lam N (j + 1) x) = prodE E lam N j (A x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [ih, map_sub, map_smul, h]
    congr 1
    push_cast
    module

theorem killed_stable (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (N : ℕ) :
    ∀ (t : ℂ) (x : M), Killed a N x → Killed a N (E x - t • x) := by
  induction N with
  | zero => intro t x hx; rw [killed_zero] at hx ⊢; simp [hx]
  | succ N ih =>
    intro t x hx
    rw [killed_succ] at hx ⊢
    intro i
    have e : a i (E x - t • x) = E (a i x) - (t - lam) • a i x := by
      rw [map_sub, map_smul, h]; module
    rw [e]
    exact ih _ _ (hx i)

theorem prodE_kills (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (h0 : ∀ x, (∀ i, a i x = 0) → E x = 0) (N : ℕ) :
    ∀ x : M, Killed a N x → prodE E lam N 0 x = 0 := by
  induction N with
  | zero => intro x hx; exact (killed_zero a x).1 hx
  | succ N ih =>
    intro x hx
    rw [killed_succ] at hx
    simp only [prodE, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
    rw [prodE_comm]
    refine h0 _ fun i => ?_
    rw [shift_prodE E (a i) lam (h i), ih _ (hx i)]

theorem peel (E : Module.End ℂ M) (lam : ℂ) (hl : lam ≠ 0) (S : M → Prop) (P : Submodule ℂ M)
    (hS : ∀ (t : ℂ) x, S x → S (E x - t • x)) (hE : ∀ x, S x → E x ∈ P) (K : ℕ) :
    ∀ (j : ℕ) (x : M), S x → prodE E lam K (j + 1) x ∈ P → x ∈ P := by
  induction K with
  | zero => intro j x _ hx; exact hx
  | succ K ih =>
    intro j x hx hp
    simp only [prodE] at hp
    have h1 := ih _ _ (hS _ x hx) hp
    have h2 := P.sub_mem (hE x hx) h1
    rw [sub_sub_cancel] at h2
    exact (P.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) hl)).1 h2

theorem mem_of_killed : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  intro I M _ _ a c n e lam hl hc P hv hP N
  set E : Module.End ℂ M := ∑ k, c (e k) * a (e k) with hEdef
  have hEx : ∀ x, E x = ∑ k, c (e k) (a (e k) x) := by
    intro x; simp [hEdef, LinearMap.sum_apply]
  have h : ∀ i x, a i (E x) = E (a i x) + lam • a i x := by
    intro i x
    have := LinearMap.congr_fun (hc i) x
    simpa using this
  have h0 : ∀ x, (∀ i, a i x = 0) → E x = 0 := by
    intro x hx; simp [hEx, hx]
  induction N with
  | zero => intro m hm; rw [(killed_zero a m).1 hm]; exact P.zero_mem
  | succ N ih =>
    intro m hm
    refine peel E lam hl (Killed a (N + 1)) P (killed_stable a E lam h (N + 1)) (fun x hx => ?_) N 0 m hm
      (hv _ fun i => ?_)
    · rw [hEx]
      exact P.sum_mem fun k _ => hP _ _ (ih _ ((killed_succ a N x).1 hx _))
    · rw [shift_prodE E (a i) lam (h i)]
      exact prodE_kills a E lam h h0 N _ ((killed_succ a N m).1 hm i)

end GlobalTheory.FockCompare.WeylInduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  first | exact @GlobalTheory.FockCompare.WeylInduct.mem_of_killed | exact GlobalTheory.FockCompare.WeylInduct.mem_of_killed | (intros; apply GlobalTheory.FockCompare.WeylInduct.mem_of_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumber
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.Imports
namespace GlobalTheory.PolynomialCoeffEq

open Module

theorem coeff_eq {R : Type} [AddCommGroup R] [Module ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) {n : ℕ} (v : Basis (Fin n) ℝ R)
    (hv : ∀ i j, i ≠ j → g (v i) (v j) = 0) (x : R) (k : Fin n) :
    g x (v k) = v.repr x k * g (v k) (v k) := by
  conv_lhs => rw [← v.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · intro i _ hik
    rw [hv i k hik, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem main : ∀ {R : Type} [inst : AddCommGroup R] [inst_1 : Module ℝ R] [FiniteDimensional ℝ R] (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ (u v : R), ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) v = ((g : R → R →ₗ[ℝ] ℝ) v : R → ℝ) u) → (∀ (u : R), u ≠ (0 : R) → (0 : ℝ) < ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) u) → ∃ (n : ℕ) (e : Fin n → R), ∀ (x : R), ∑ k : Fin n, ((g : R → R →ₗ[ℝ] ℝ) x : R → ℝ) (e k) • e k = x := by
  intro R _ _ _ g hsym hpos
  have h2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g) ⟨hsym⟩
  have hv' : ∀ i j, i ≠ j → g (v i) (v j) = 0 := LinearMap.BilinForm.iIsOrtho_def.mp hv
  have hpos' : ∀ k, 0 < g (v k) (v k) := fun k => hpos _ (v.ne_zero k)
  refine ⟨_, fun k => (Real.sqrt (g (v k) (v k)))⁻¹ • v k, fun x => ?_⟩
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, coeff_eq g v hv' x k, smul_smul]
  congr 1
  have hs := Real.mul_self_sqrt (hpos' k).le
  have he : (Real.sqrt (g (v k) (v k)))⁻¹ * (v.repr x k * g (v k) (v k)) *
      (Real.sqrt (g (v k) (v k)))⁻¹ =
      v.repr x k * (g (v k) (v k) * (Real.sqrt (g (v k) (v k)) * Real.sqrt (g (v k) (v k)))⁻¹) := by
    ring
  rw [he, hs, mul_inv_cancel₀ (hpos' k).ne', mul_one]

end GlobalTheory.PolynomialCoeffEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumber
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeylNumber

theorem exists_parseval_family {R : Type} [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u) :
    ∃ (n : ℕ) (e : Fin n → R), ∀ x, ∑ k, g x (e k) • e k = x := by
  first
  | exact @_root_.GlobalTheory.PolynomialCoeffEq.main
  | exact _root_.GlobalTheory.PolynomialCoeffEq.main
  | (apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialCoeffEq.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialCoeffEq.main ..)

theorem weyl_number : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  intro M R _ _ _ _ _ Dop om κ j hadd hsmul hκ hcomm hanti hjj hom hpos
  have h1 : ∀ u v, om (j u) v = -om u (j v) := fun u v => by
    rw [← hom (j u) v, hjj]; simp
  have hc : ∀ u v, Dop u * Dop v = Dop v * Dop u + (κ * (om u v : ℝ)) • (1 : Module.End ℂ M) :=
    fun u v => by rw [← hcomm]; abel
  have hneg : ∀ u, Dop (-u) = -Dop u := fun u => by
    have := hsmul (-1) u
    simpa using this
  have hac : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) =
      (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) +
        (2 * κ * ((om u v : ℝ) - Complex.I * (om u (j v) : ℝ))) • (1 : Module.End ℂ M) := by
    intro u v
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  have haa : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v + Complex.I • Dop (j v)) =
      (Dop v + Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) := by
    intro u v
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  refine ⟨fun u v => ⟨_, by rw [hac u v, add_sub_cancel_left]⟩, ?_⟩
  obtain ⟨n, e, he⟩ := exists_parseval_family (om.compl₂ j)
    (fun u v => by
      simp only [LinearMap.compl₂_apply]
      rw [hanti (j u) v, h1, neg_neg])
    (fun u hu => by simpa using hpos u hu)
  simp only [LinearMap.compl₂_apply] at he
  let A : R →+ Module.End ℂ M := AddMonoidHom.mk' (fun u => Dop u + Complex.I • Dop (j u))
    (fun u v => by simp only [map_add (f := _), hadd, smul_add]; abel)
  have hA : ∀ u, A u = Dop u + Complex.I • Dop (j u) := fun _ => rfl
  have hAs : ∀ (c : ℝ) u, A (c • u) = (c : ℂ) • A u := fun c u => by
    simp only [hA, map_smul, hsmul]; module
  have hAj : ∀ u, A (j u) = (-Complex.I) • A u := fun u => by
    simp only [hA, hjj, hneg, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  have hsum : ∀ x, ∑ k, ((om x (j (e k)) : ℝ) : ℂ) • A (e k) = A x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← he x, map_sum]
    simp only [hAs]
  refine ⟨n, e, -4 * Complex.I * κ, by simp [hκ], fun u => ?_⟩
  have key : ∀ k, A u * ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) =
      ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) * A u +
        ((2 * κ) • (((om (j u) (j (e k)) : ℝ) : ℂ) • A (e k))
          - (2 * κ * Complex.I) • (((om u (j (e k)) : ℝ) : ℂ) • A (e k))) := fun k => by
    rw [← mul_assoc, hA u, hac, add_mul, mul_assoc, mul_assoc, hA (e k), haa u, hom,
      smul_mul_assoc, one_mul]
    module
  simp only [← hA]
  rw [Finset.mul_sum, add_mul, Finset.sum_mul, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    hsum, hsum, hAj, smul_mul_assoc, one_mul]
  module

end GlobalTheory.WeylNumber
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumberStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalCommutationRelations_weylNumber : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  first | exact @GlobalTheory.WeylNumber.weyl_number | exact GlobalTheory.WeylNumber.weyl_number | (intros; apply GlobalTheory.WeylNumber.weyl_number <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantCongruencesImaginaryQuadratic
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.WeberCongruence

theorem mem_of_isIntegral (W : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ W := by
  have h1 : IsIntegral W x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact y.2

theorem mem_of_pow_mem (W : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at hx ⊢
  rw [map_pow] at hx
  exact (pow_le_one_iff_of_nonneg zero_le hn).mp hx

theorem mul_mem_nonunits (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∈ W.nonunits) (hy : y ∈ W) :
    x * y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx ⊢
  rw [← W.valuation_le_one_iff] at hy
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy

theorem mem_nonunits_of_mul (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∉ W.nonunits)
    (h : x * y ∈ W.nonunits) : y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx h ⊢
  rw [map_mul] at h
  by_contra hy
  exact absurd h (not_lt.mpr (one_le_mul_of_one_le_of_one_le (not_lt.mp hx) (not_lt.mp hy)))

theorem sub_mem_nonunits_iff (W : ValuationSubring ℂ) (x y : W) :
    (x : ℂ) - y ∈ W.nonunits ↔ IsLocalRing.residue W x = IsLocalRing.residue W y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem charP_residueField (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) : CharP (IsLocalRing.ResidueField W) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have := (sub_mem_nonunits_iff W (p : W) 0).mp (by simpa using h)
  simpa using this

theorem inv_natCast_mem (W : ValuationSubring ℂ) {p m : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) (hm : ¬ p ∣ m) : (m : ℂ)⁻¹ ∈ W := by
  have := charP_residueField W hp h
  have h1 : (m : ℂ) ∉ W.nonunits := fun hc ↦ by
    have := (sub_mem_nonunits_iff W (m : W) 0).mp (by simpa using hc)
    rw [map_natCast, map_zero, CharP.cast_eq_zero_iff _ p] at this
    exact hm this
  rw [ValuationSubring.mem_nonunits_iff_or] at h1
  push Not at h1
  exact h1.2

theorem pow_six_eq_one {k : Type*} [CommRing k] {p : ℕ} (hp : p.Prime) [CharP k p] {g h a : k}
    (e : g ^ 3 - 27 * h ^ 2 = 1) (h2 : g = a ^ 2 * g ^ p) (h3 : h = a ^ 3 * h ^ p) :
    a ^ 6 = 1 := by
  have := Fact.mk hp
  have e1 := congrArg (frobenius k p) e
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, frobenius_def] at e1
  generalize g ^ p = G at *
  generalize h ^ p = H at *
  subst h2 h3
  linear_combination e - a ^ 6 * e1

theorem congruences (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    {g h a : ℂ} (hg : g ∈ W) (hh : h ∈ W) (ha : a ∈ W) (e : g ^ 3 - 27 * h ^ 2 = 1)
    (h2 : g - a ^ 2 * g ^ p ∈ W.nonunits) (h3 : h - a ^ 3 * h ^ p ∈ W.nonunits) :
    g ^ 3 - (g ^ 3) ^ p ∈ W.nonunits ∧ ∀ x y, x ∈ W → y - a * x ^ p ∈ W.nonunits →
      g * h * y - (g * h * x) ^ p ∈ W.nonunits := by
  have := charP_residueField W hp hW
  lift g to W using hg
  lift h to W using hh
  lift a to W using ha
  have e' : g ^ 3 - 27 * h ^ 2 = 1 := Subtype.ext e
  have e1 := congrArg (IsLocalRing.residue W) e'
  have e2 := (sub_mem_nonunits_iff W g (a ^ 2 * g ^ p)).mp h2
  have e3 := (sub_mem_nonunits_iff W h (a ^ 3 * h ^ p)).mp h3
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat] at e1 e2 e3
  have e4 := pow_six_eq_one hp e1 e2 e3
  refine ⟨(sub_mem_nonunits_iff W (g ^ 3) ((g ^ 3) ^ p)).mpr ?_, fun x y hx hy ↦ ?_⟩
  · simp only [map_pow]
    rw [← pow_mul _ 3 p, mul_comm 3 p, pow_mul]
    generalize IsLocalRing.residue W g ^ p = G at *
    rw [e2]
    linear_combination G ^ 3 * e4
  · lift x to W using hx
    have hy' : y ∈ W := by
      have := add_mem (W.nonunits_subset hy) (a * x ^ p).2
      simpa using this
    lift y to W using hy'
    have e5 := (sub_mem_nonunits_iff W y (a * x ^ p)).mp hy
    refine (sub_mem_nonunits_iff W (g * h * y) ((g * h * x) ^ p)).mpr ?_
    simp only [map_mul, map_pow, mul_pow] at e5 ⊢
    generalize IsLocalRing.residue W g ^ p = G at *
    generalize IsLocalRing.residue W h ^ p = H at *
    rw [e2, e3, e5]
    linear_combination G * H * IsLocalRing.residue W x ^ p * e4

theorem norm_sq_eq_absNorm {K : Type*} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (π : 𝓞 K) :
    ‖σ π‖ ^ 2 = Ideal.absNorm (Ideal.span {π}) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk σ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), Odd m → ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := GlobalTheory.T.weierstrassP_complexMultiplication_congruence_mod_prime L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hm hpm ↦ ?_⟩
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := GlobalTheory.T.weierstrassP_torsion_integral_and_distinct_mod L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruence
end
