module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolume

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonne
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign.TopPos

open GlobalTheory.GoodMetric.LinSubst

variable {n : ℕ}

def pairForm (u v : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ p : Fin n × Fin n, C (u p.1 * starRingEnd ℂ (v p.2)) * X p

theorem topCoeff_prod_pairForm_fin (k : ℕ) :
    ∃ D : (Fin k → Fin n → ℂ) → ℂ, ∀ u v : Fin k → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  by_cases hk : k = n
  · subst hk
    refine ⟨fun u => (Matrix.of u).det, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, u i (c i) * starRingEnd ℂ (v i (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (Matrix.of u) i (c i)) * (rowSel c).det) *
        ((∏ i, ((Matrix.of v).map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [Matrix.of_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, RingHom.map_det]
    rfl
  · refine ⟨fun _ => 0, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    simp [topCoeff_prod_X_of_ne hk]

theorem topCoeff_prod_pairForm (J : Type) [Fintype J] :
    ∃ D : (J → Fin n → ℂ) → ℂ, ∀ u v : J → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm_fin (n := n) (Fintype.card J)
  let e := (Fintype.equivFin J).symm
  refine ⟨fun u => D (u ∘ e), fun u v => ?_⟩
  rw [← hD, ← e.prod_comp]
  rfl

theorem factorial_mul_det {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (m.factorial : R) * M.det = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) := by
  rw [Finset.sum_comm]
  have h (τ : Equiv.Perm (Fin m)) : ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    have h2 : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : R) * ∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, (M.submatrix id τ) (σ i) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [Matrix.submatrix_apply, id]
          ring
      _ = M.det := by rw [h1, ← mul_assoc, h2, one_mul]
  simp_rw [h]
  simp [Fintype.card_perm]

theorem sqPoly_apply {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (i j : Fin m) :
    sqPoly T i j = ∑ k, pairForm (fun a => T (coordVec a) i k) (fun a => T (coordVec a) j k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sqPoly, pairForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (γ := Fin r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (γ := Fin r)]
  rfl

theorem factorial_mul_det_sqPoly {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    C (m.factorial : ℂ) * (sqPoly T).det = ∑ k : Fin m → Fin r, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      C (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ i, pairForm (fun a => T (coordVec a) (σ i) (k i)) (fun a => T (coordVec a) (τ i) (k i)) := by
  rw [map_natCast, factorial_mul_det]
  simp_rw [sqPoly_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  simp only [map_mul, map_intCast]

theorem topCoeff_prod_det_nonneg {B : Type} [Fintype B] (m r : B → ℕ)
    (T : ∀ b, V n →ₗ[ℂ] Matrix (Fin (m b)) (Fin (r b)) ℂ) :
    0 ≤ topCoeff (∏ b, (sqPoly (T b)).det) := by
  classical
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm (n := n) (Σ b, Fin (m b))
  have h : (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) =
      ∑ k : ∀ b, Fin (m b) → Fin (r b),
        (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) *
        starRingEnd ℂ (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) := by
    rw [← topCoeff_C_mul, map_prod, ← Finset.prod_mul_distrib]
    simp_rw [factorial_mul_det_sqPoly]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, ← Fintype.prod_sigma', hD, Finset.prod_mul_distrib]
    simp only [map_mul, map_prod, map_intCast]
    ring
  have h0 : 0 ≤ (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) := by
    rw [h]
    exact Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hN : (0 : ℝ) < ∏ b, ((m b).factorial : ℝ) :=
    Finset.prod_pos fun b _ => by exact_mod_cast Nat.factorial_pos _
  have e : (∏ b, ((m b).factorial : ℂ)) = ((∏ b, ((m b).factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e] at h0
  have h1 : (0 : ℂ) ≤ (((∏ b, ((m b).factorial : ℝ))⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hN.le)
  have h2 := mul_nonneg h1 h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne', Complex.ofReal_one, one_mul] at h2

end GlobalTheory.PointFormSign.TopPos

theorem GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ)
    (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ) :
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  have h := TopPos.topCoeff_prod_det_nonneg (B := Σ t, Fin (e t)) (fun b => m b.1) (fun b => r b.1) fun b => T b.1
  rw [Fintype.prod_sigma] at h
  refine h.trans_eq (congrArg topCoeff (Finset.prod_congr rfl fun t _ => ?_))
  exact (Finset.prod_const (s := Finset.univ) (sqPoly (T t)).det).trans (by rw [Finset.card_univ, Fintype.card_fin])
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonneStatement
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg : ∀ {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ) (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ),
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  first | exact @GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | exact GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | (intros; apply GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeG
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeG
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign.DomCurv

section Sqrt

open scoped MatrixOrder

theorem exists_eq_conjTranspose_mul_self {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin k) (Fin k) ℂ, T = Bᴴ * B := by
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

end Sqrt

variable {m r : ℕ}

def domForm (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - Matrix.of x * (Matrix.of x)ᴴ

theorem domGram_eq (x : Fin m → Fin r → ℂ) : domGram m r x = ((domForm m r x)⁻¹)ᵀ := rfl

theorem mContDiffAt_of (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) y := fun a b => by
  show ContDiffAt ℝ k (fun x : Fin m → Fin r → ℂ => x a b) y
  exact ((contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin r → ℂ)) a)).contDiffAt

theorem mdel_of (y ξ : Fin m → Fin r → ℂ) :
    mdel (fun y : Fin m → Fin r → ℂ => Matrix.of y) y ξ = Matrix.of ξ := by
  ext a b
  show del (fun x : Fin m → Fin r → ℂ => x a b) y ξ = ξ a b
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, del_eq_fderiv (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_of (y η : Fin m → Fin r → ℂ) :
    mdbar (fun y : Fin m → Fin r → ℂ => Matrix.of y) y η = 0 := by
  ext a b
  show dbar (fun x : Fin m → Fin r → ℂ => x a b) y η = 0
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem mContDiffAt_domForm (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (domForm m r) y :=
  (mContDiffAt_const 1).sub ((mContDiffAt_of k y).mul (mContDiffAt_of k y).conjTranspose)

theorem domForm_eq_fun : domForm m r = fun y => 1 + -(Matrix.of y * (Matrix.of y)ᴴ) := by
  funext y; simp [domForm, sub_eq_add_neg]

theorem mdel_domForm (y ξ : Fin m → Fin r → ℂ) :
    mdel (domForm m r) y ξ = -(Matrix.of ξ * (Matrix.of y)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdel_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdel_const,
    mdel_neg, mdel_mul h1 h1.conjTranspose, mdel_conjTranspose, mdbar_of, mdel_of]
  simp

theorem mdbar_domForm (y η : Fin m → Fin r → ℂ) :
    mdbar (domForm m r) y η = -(Matrix.of y * (Matrix.of η)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdbar_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdbar_const,
    mdbar_neg, mdbar_mul h1 h1.conjTranspose, mdbar_conjTranspose, mdbar_of, mdel_of]
  simp

theorem conn_domGram {y : Fin m → Fin r → ℂ} (hu : IsUnit (domForm m r y).det)
    (ξ : Fin m → Fin r → ℂ) :
    conn (domGram m r) y ξ = Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) := by
  have e : (fun x => (domGram m r x)ᵀ) = fun x => (domForm m r x)⁻¹ := by
    funext x; rw [domGram_eq, transpose_transpose]
  have e2 : (domGram m r y)ᵀ = (domForm m r y)⁻¹ := congrFun e y
  rw [conn, e2, ← mdel_transpose, e, mdel_inv (mContDiffAt_domForm 1 y) hu, mdel_domForm,
    nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]

theorem curv_domGram_eq {x : Fin m → Fin r → ℂ} (hx : IsUnit (domForm m r x).det)
    (ξ η : Fin m → Fin r → ℂ) :
    curv (domGram m r) x ξ η = -(Matrix.of ξ * ((1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ *
      Matrix.of x) * ((Matrix.of η)ᴴ * (domForm m r x)⁻¹))) := by
  have hev := (mContDiffAt_domForm (m := m) (r := r) 1 x).eventually_isUnit hx
  have he : (fun y => conn (domGram m r) y ξ) =ᶠ[𝓝 x]
      fun y => Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) :=
    hev.mono fun y hy => conn_domGram hy ξ
  have hZ := mContDiffAt_of (m := m) (r := r) 1 x
  have hM := (mContDiffAt_domForm (m := m) (r := r) 1 x).inv hx
  rw [curv, mdbar_congr he, mdbar_mul (mContDiffAt_const (Matrix.of ξ)) (hZ.conjTranspose.mul hM),
    mdbar_const, mdbar_mul hZ.conjTranspose hM, mdbar_inv (mContDiffAt_domForm 1 x) hx,
    mdbar_domForm, mdbar_conjTranspose, mdel_of]
  simp only [Matrix.zero_mul, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_add]
  rw [add_comm]

end GlobalTheory.PointFormSign.DomCurv

namespace GlobalTheory.PointFormSign


open DomCurv in
theorem curv_domGram_isNegSq (m r : ℕ) (x : Fin m → Fin r → ℂ)
    (hx : (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef) : IsNegSq (curv (domGram m r) x) r := by
  have hxA : (domForm m r x).PosDef := hx
  have hu : IsUnit (domForm m r x).det := (isUnit_iff_isUnit_det _).1 hxA.isUnit
  have hM := hxA.inv
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self hM.posSemidef
  have hQ : (1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ * Matrix.of x).PosSemidef :=
    (PosDef.one.add_posSemidef (hM.posSemidef.conjTranspose_mul_mul_same (Matrix.of x))).posSemidef
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hQ
  have hBu : IsUnit B.det := by
    have h1 : IsUnit (Bᴴ * B).det := by rw [← hB]; exact (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  let T : (Fin m → Fin r → ℂ) →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ :=
    { toFun := fun ξ => B * Matrix.of ξ * Cᴴ
      map_add' := fun ξ ξ' => by
        show B * Matrix.of (ξ + ξ') * Cᴴ = B * Matrix.of ξ * Cᴴ + B * Matrix.of ξ' * Cᴴ
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c ξ => by
        show B * (c • Matrix.of ξ) * Cᴴ = c • (B * Matrix.of ξ * Cᴴ)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨B, T, hBu, fun ξ η => ?_⟩
  rw [curv_domGram_eq hu, hC, hB]
  show -(Matrix.of ξ * ((Cᴴ * C) * ((Matrix.of η)ᴴ * (Bᴴ * B)))) =
    B⁻¹ * (-((B * Matrix.of ξ * Cᴴ) * (B * Matrix.of η * Cᴴ)ᴴ)) * B
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hBu]

end GlobalTheory.PointFormSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeGStatement
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  first | exact @GlobalTheory.PointFormSign.curv_domGram_isNegSq | exact GlobalTheory.PointFormSign.curv_domGram_isNegSq | (intros; apply GlobalTheory.PointFormSign.curv_domGram_isNegSq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameC
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameC
set_option autoImplicit false

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign

theorem mContDiffAt_domGram {m r : ℕ} {k : WithTop ℕ∞} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : MContDiffAt k (domGram m r) x := by
  have h : MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) x := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  exact (((mContDiffAt_const 1).sub (h.mul h.conjTranspose)).inv hx).transpose

theorem isUnit_det_domGram {m r : ℕ} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : IsUnit (domGram m r x).det := by
  rw [domGram, det_transpose]
  exact isUnit_nonsing_inv_det _ hx

theorem isNegSq_curv_of_changeFrame_comp {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n)
    (W : V n → Matrix (Fin m) (Fin m) ℂ) (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ) (hκ : 0 < κ)
    (hG : ∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ))
    (hZ : ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u)
    (hW : ∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u)
    (hWu : IsUnit (W v).det) (hpos : (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef)
    (hneg : IsNegSq (curv (domGram m r) (Z v)) r) : IsNegSq (curv G v) r := by
  obtain ⟨S, T, hS, hF⟩ := hneg
  have hu : IsUnit (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).det :=
    (isUnit_iff_isUnit_det _).1 hpos.isUnit
  have hD2 : MContDiffAt 2 (domGram m r) (Z v) := mContDiffAt_domGram _ hu
  have hDu : IsUnit (domGram m r (Z v)).det := isUnit_det_domGram _ hu
  have hZ2 : ContDiffAt ℂ 2 Z v := (GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hZ).contDiffAt
  have hW2 : MContDiffAt 2 W v := fun i j =>
    ((GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 (hW i j)).contDiffAt (n := 2)).restrict_scalars ℝ
  have hW0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar W x η = 0 := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hW i j]
      with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b)]
    rfl
  have hH2 : MContDiffAt 2 (fun x => domGram m r (Z x)) v :=
    fun a b => (hD2 a b).comp v (hZ2.restrict_scalars ℝ)
  have hK2 : MContDiffAt 2 (fun u => (W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ) v :=
    (hW2.transpose.mul hH2).mul hW2.conjTranspose.transpose
  have hKu : IsUnit ((W v)ᵀ * domGram m r (Z v) * (W v)ᴴᵀ).det := by
    simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hWu.mul hDu).mul hWu.star
  refine ⟨S * W v, T ∘ₗ (fderiv ℂ Z v).toLinearMap, by rw [det_mul]; exact hS.mul hWu, fun ξ η => ?_⟩
  rw [curv_congr hG, curv_smul (f := fun _ => κ) contDiffAt_const hκ.ne' hK2 hKu, leviForm_const,
    curv_changeFrame (H := fun x => domGram m r (Z x)) hH2 hDu hW2 hWu hW0,
    curv_comp_holo hD2 hDu hZ2, hF, Matrix.mul_inv_rev]
  simp [Matrix.mul_assoc]

end GlobalTheory.PointFormSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameCStatement
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  first | exact @GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | exact GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | (intros; apply GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquareStatement
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  first | exact @GlobalTheory.PointFormSign.chernPoly_top_of_negSq | exact GlobalTheory.PointFormSign.chernPoly_top_of_negSq | (intros; apply GlobalTheory.PointFormSign.chernPoly_top_of_negSq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonneg
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

theorem chernTop_pointPoly_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    {n : ℕ} (G : V n → Mat Dw.mult ℂ) (v : V n)
    (h : ∀ τ : GlobalTheory.AllWt.Psi H, IsNegSq (curv (fun u => G u τ.1) v) (Dw.p + Dw.q - Dw.mult τ.1)) :
    0 ≤ chernTop (pointPoly H Dw) G v := by
  choose S T hS hF using h
  have key : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (sqPoly (T τ)).det ^ (Dw.p + Dw.q - Dw.mult τ.1) := by
    rw [pointPoly, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_C, aeval_X, GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare _ _ _ _ (hS τ) (hF τ)]
    congr 1
    simp only [map_pow, map_neg, map_one]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have h0 : 0 ≤ topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw)) := by
    rw [key]; exact GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg _ _ _ T
  have hre : 0 ≤ (topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw))).re :=
    (Complex.nonneg_iff.1 h0).1
  unfold chernTop
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg Real.pi_pos.le _)) hre

end GlobalTheory.PointFormSign

theorem GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA
  refine GlobalTheory.PointFormSign.chernTop_pointPoly_nonneg H Dw _ _ fun τ => ?_
  obtain ⟨κ, W, Z, hκ, hG, hZ, hW, hWu, hZd⟩ := GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ
  exact GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange _ _ W Z κ hκ hG hZ hW hWu hZd (GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram _ _ _ hZd)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonnegStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  first | exact @GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg | exact GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg | (intros; apply GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen
open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory

theorem iSup_measure_apply_eq_zero {α κ : Type*} [MeasurableSpace α] (μ : κ → Measure α) {S : Set α}
    (hS : MeasurableSet S) (h : ∀ i, μ i S = 0) : (⨆ i, μ i) S = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => ?_
    calc μ i = (μ i).restrict Sᶜ :=
          (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (h i))).symm
      _ ≤ (⨆ i, μ i).restrict Sᶜ := Measure.restrict_mono subset_rfl (le_iSup μ i)
  refine le_antisymm ?_ (zero_le)
  calc (⨆ i, μ i) S ≤ (⨆ i, μ i).restrict Sᶜ S := Measure.le_iff'.1 hle S
    _ = 0 := by rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

theorem chernTopPart_neg_eq_zero_of_nonneg {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R : MvPolynomial (ι × ℕ) ℝ)
    (h : ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) :
    chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  unfold chernTopPart glueMeas
  refine iSup_measure_apply_eq_zero _ hS fun c => ?_
  rw [chartMeas_apply c.e _ hS]
  have hm : MeasurableSet (c.e '' (c.e.source ∩ ptsIn X.str σ O)) :=
    measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) Set.inter_subset_left
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
  rintro _ ⟨y, ⟨hys, hyS⟩, rfl⟩
  have hz : c.e.symm (c.e y) ∈ c.e.source ∩ ptsIn X.str σ O := by
    rw [c.e.left_inv hys]; exact ⟨hys, hyS⟩
  beta_reduce
  generalize c.e.symm (c.e y) = z at hz ⊢
  apply ENNReal.ofReal_eq_zero.2
  have := h z hz.2 c hz.1 _ (E.nonempty (under z)).choose_spec
  push_cast
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpenStatement
open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ), (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y), 0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) → chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  first | exact @GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | exact GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | (intros; apply GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_pointPoly_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw) (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have h0 := GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw)
    (GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL)
  have h1 := GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have hc := (GlobalTheory.TrueCx.covol_pos (U.X k)).le
  refine ⟨fun ε => ?_, ?_⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [h1]; exact ENNReal.ofReal_ne_top
    · rw [h0]; exact ENNReal.zero_ne_top
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, h1, h0, ENNReal.toReal_ofReal hc]; simp

end GlobalTheory.LieBase
