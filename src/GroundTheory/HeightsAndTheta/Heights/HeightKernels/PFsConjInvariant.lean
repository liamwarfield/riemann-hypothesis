module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudyConjugationInvariant

theorem fsMetric_conj {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric (ι := n)).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric (ι := n)).ρ w := by
  simp [fsMetric, EuclideanSpace.norm_eq]

end FubiniStudyConjugationInvariant

theorem FsConjInvariant.proof : FsConjInvariant.Statement := by
  intro K _ ι _ z
  simp only [fsMulti, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaNormMajorant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaNormMajorant

theorem isSymm_of_posDef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by
  have h := hY.isHermitian
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

end KThetaNormMajorant

theorem ThetaNormMajorant.proof (h : ThetaSummandNorm.Statement) : ThetaNormMajorant.Statement := by
  intro g X Y a b u₁ u₂ hY
  have hS := KThetaNormMajorant.isSymm_of_posDef hY
  set z : Fin g → ℂ := periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ) with hz
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  have hterm : ∀ k : Fin g → ℤ,
      ‖thetaSummand X Y a b z k‖ = exp (-π * qf Y (intVec k + a + u₁)) * E⁻¹ := by
    intro k
    rw [← h g X Y a b u₁ u₂ k hS, mul_inv_cancel_right₀ hEpos.ne']
  have hG : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π Real.pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hsum : Summable fun k : Fin g → ℤ => ‖thetaSummand X Y a b z k‖ := by
    simp_rw [hterm]
    exact hG.mul_right _
  have hN : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b z k‖ * E := rfl
  rw [hN]
  calc ‖∑' k, thetaSummand X Y a b z k‖ * E
      ≤ (∑' k, ‖thetaSummand X Y a b z k‖) * E :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) hEpos.le
    _ = ∑' k, ‖thetaSummand X Y a b z k‖ * E := (tsum_mul_right).symm
    _ = ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := by
        congr 1; funext k
        rw [hterm, inv_mul_cancel_right₀ hEpos.ne']

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianRootBound

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def cone {R : Type*} [CommRing R] (y : (Σ k, ι k) → R) : MRing ι →ₐ[ℤ] MvPolynomial K R :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem map_cone {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [cone]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [cone]

theorem eval_grassPolyCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by
  let φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ :=
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom
  show φ _ = _
  rw [grassPolyCoord, RingHom.map_det, rootCoord]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)
  · simp [Fin.append_left, Matrix.one_apply, apply_ite φ]
  · simp [Fin.append_right, φ]

end GrassmannianRootBound


open GrassmannianRootBound in
theorem GrassLeRoot.proof : GrassLeRoot.Statement := by
  intro f j m ζ g hg
  have h0 : mConeMap (grassCoord f j m) g = 0 := hg
  have h1 : cone (grassPolyCoord f j m) g = 0 := by
    apply MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m))
      (IsFractionRing.injective _ _)
    rw [map_cone, map_zero]
    exact h0
  have h2 := congrArg (MvPolynomial.map
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1
  rw [map_cone, map_zero] at h2
  show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0
  simpa [cone, eval_grassPolyCoord] using h2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaInnerMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

namespace KThetaInnerMean

theorem thetaSummand_shift {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by
  unfold thetaSummand torusChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero,
    mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

end KThetaInnerMean


open KThetaInnerMean in
theorem ThetaInnerMean.proof (h₁ : ThetaSummandNorm.Statement) (h₂ : ThetaCubeParseval.Statement) :
    ThetaInnerMean.Statement := by
  intro g X Y a b u₁ hY
  have hS : Y.IsSymm := by
    have h := hY.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  set c : (Fin g → ℤ) → ℂ := fun k => thetaSummand X Y a b
    (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k with hc
  have hcE : ∀ k, ‖c k‖ * E = exp (-π * qf Y (intVec k + a + u₁)) := fun k =>
    h₁ g X Y a b u₁ 0 k hS
  have hcs : Summable fun k => ‖c k‖ := by
    have hs := (KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)).mul_right E⁻¹
    refine hs.congr fun k => ?_
    rw [← add_assoc, ← hcE k, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  have hN : ∀ u₂, thetaNorm X Y a b u₁ u₂ ^ 2 = ‖∑' k, c k * torusChar k u₂‖ ^ 2 * E ^ 2 := by
    intro u₂
    have h : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * E := rfl
    rw [h, tsum_congr (fun k => thetaSummand_shift X Y a b u₁ u₂ k), tsum_mul_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_pow _ _ _
  simp only [hN]
  rw [integral_mul_const, h₂ g c hcs, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [← mul_pow, hcE k, ← exp_nat_mul]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_star_mul_self {U : Matrix n n ℂ} (hU : star U * U = 1) : U.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hU
  rw [det_mul, h, mul_zero, det_one] at this
  exact zero_ne_one this

theorem exists_congr_eq_one {N : Matrix n n ℂ} (hN : N.PosDef) :
    ∃ C : Matrix n n ℂ, C.det ≠ 0 ∧ Cᴴ * N * C = 1 := by
  set U : Matrix n n ℂ := (hN.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set μ := hN.1.eigenvalues
  set d : n → ℂ := fun j => (((Real.sqrt (μ j))⁻¹ : ℝ) : ℂ) with hd
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hN' : N = U * diagonal (fun j => (μ j : ℂ)) * star U := hN.1.spectral_theorem
  have hμ : ∀ j, 0 < μ j := hN.eigenvalues_pos
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero (det_ne_zero_of_star_mul_self hU) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
    have := Real.sqrt_pos.mpr (hμ j)
    simp only [hd, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact this.ne'
  · have hstar : Uᴴ = star U := rfl
    rw [hN', conjTranspose_mul, diagonal_conjTranspose, hstar]
    calc diagonal (star d) * star U * (U * diagonal (fun j => (μ j : ℂ)) * star U) * (U * diagonal d)
        = diagonal (star d) * (star U * U) * diagonal (fun j => (μ j : ℂ)) * (star U * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext j
          have hs := Real.sqrt_pos.mpr (hμ j)
          have hsq := Real.sq_sqrt (hμ j).le
          simp only [hd, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
          congr 1
          field_simp
          linarith

theorem det_congr (C X : Matrix n n ℂ) :
    (Cᴴ * X * C).det = (Complex.normSq C.det : ℂ) * X.det := by
  rw [det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end ChartEnergyCongruence


open ChartEnergyCongruence in
theorem ChartEnergy.proof (hI : ChartEnergyLinearInvariant.Statement) (hD : ChartEnergyDiagonal.Statement) :
    ChartEnergy.Statement := by
  intro e M N hM hN
  obtain ⟨C, hC, hCN⟩ := exists_congr_eq_one hN
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)
  have hM' : (Cᴴ * M * C).PosDef := hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hCu)
  set M' := Cᴴ * M * C with hM'def
  set V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := (hM'.1.eigenvectorUnitary : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
  set Λ := hM'.1.eigenvalues
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVd : V.det ≠ 0 := det_ne_zero_of_star_mul_self hVV
  have hdiag : Vᴴ * M' * V = diagonal (fun j => (Λ j : ℂ)) := by
    have := hM'.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hone : Vᴴ * 1 * V = 1 := by rw [Matrix.mul_one]; exact hVV
  have hterm : ∀ k, chartMixedEnergy M N k = chartMixedEnergy (diagonal fun j => (Λ j : ℂ)) 1 k := by
    intro k
    rw [← hI e M N C hM hN hC k, hCN, ← hI e M' 1 V hM' PosDef.one hVd k, hdiag, hone]
  rw [Finset.sum_congr rfl fun k _ => hterm k, hD e Λ hM'.eigenvalues_pos]

  have hMpos := (Complex.pos_iff.mp hM.det_pos).1
  have hNpos := (Complex.pos_iff.mp hN.det_pos).1
  have hns : 0 < Complex.normSq C.det := Complex.normSq_pos.mpr hC
  have hM're : M'.det.re = Complex.normSq C.det * M.det.re := by
    rw [hM'def, det_congr, Complex.re_ofReal_mul]
  have hN're : 1 = Complex.normSq C.det * N.det.re := by
    have := congrArg Complex.re (det_congr C N)
    rw [hCN, det_one, Complex.one_re, Complex.re_ofReal_mul] at this
    exact this
  have hprod : M'.det.re = ∏ j, Λ j := by
    rw [hM'.1.det_eq_prod_eigenvalues]
    change (∏ j, ((Λ j : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hlog : ∑ j, Real.log (Λ j) = Real.log M.det.re - Real.log N.det.re := by
    rw [← Real.log_prod fun j _ => (hM'.eigenvalues_pos j).ne', ← hprod, hM're,
      Real.log_mul hns.ne' hMpos.ne']
    have h1 : Real.log (Complex.normSq C.det) + Real.log N.det.re = 0 := by
      rw [← Real.log_mul hns.ne' hNpos.ne', ← hN're, Real.log_one]
    linarith
  rw [hlog]

end

end GroundTheory.Heights₂.Heights
end
