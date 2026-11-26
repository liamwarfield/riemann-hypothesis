module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularCha
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesgu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyRealDegreeAndChartDimensionEqStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOne
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.DensOne

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem det_ne_zero_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  exact_mod_cast sgn_ne X.p0 (a : ℕ)

theorem densF_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    densF X x = fun w => ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ ^ (-2 : ℤ) := by
  funext w
  unfold densF
  simp only [dmin_cpt_orth X hx]

theorem dens_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧
      ∀ τ, (mat x τ).det ≠ 0 := by
  intro E _ _ _ r X x hx
  refine ⟨?_, ?_, det_ne_zero_of_orth X hx⟩
  · rw [densF_orth X hx]
    refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
    refine ((cont_lminor X τ i.castSucc).norm.continuousAt).zpow₀ _ (Or.inl ?_)
    simp [norm_lminor_zero]
  · rw [densF_orth X hx]
    simp only [norm_lminor_zero, _root_.one_zpow, Finset.prod_const_one]

end GlobalTheory.DensOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOneStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDensity_continuousAt_zero_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧ ∀ τ, (mat x τ).det ≠ 0 := by
  first | exact @GlobalTheory.DensOne.dens_one | exact GlobalTheory.DensOne.dens_one | (intros; apply GlobalTheory.DensOne.dens_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOne
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusAngles

theorem exp_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at h
  simpa [mul_comm] using h

theorem exp_neg_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (-(Complex.I * (Complex.arg w : ℂ))) = w⁻¹ := by
  rw [Complex.exp_neg, exp_I_arg hw]

theorem exists_angles_of_prod_eq_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 →
    ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  intro r z hz hp
  rcases r with _ | n
  · exact ⟨fun _ => 0, fun a => a.elim0⟩
  · refine ⟨fun k => Complex.arg (z ⟨k, by omega⟩), fun a => ?_⟩
    unfold angles
    split_ifs with h
    · exact exp_I_arg (hz _)
    · have ha : a = Fin.last n := by ext; simp at h ⊢; omega
      subst ha
      rw [Fin.prod_univ_castSucc] at hp
      have hlast : z (Fin.last n) = (∏ k : Fin n, z k.castSucc)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right hp
      rw [hlast, Complex.ofReal_neg, Complex.ofReal_sum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
        Complex.exp_sum, ← Finset.prod_inv_distrib]
      show ∏ k : Fin n, Complex.exp (-(Complex.I * (Complex.arg (z ⟨k, _⟩) : ℂ))) = _
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [exp_neg_I_arg (hz _)]
      rfl

end GlobalTheory.TorusAngles
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOneStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 → ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  first | exact @GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | exact GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | (intros; apply GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodular
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem GlobalTheory.upperTriangular_signForm_diagonal : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  intro r b s hs hdet hup hJ
  classical
  set J : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => (s a : ℂ)) with hJdef
  have hss : ∀ a, (s a : ℂ) * (s a : ℂ) = 1 := by
    intro a; rcases hs a with h | h <;> simp [h]
  have hJJ : J * J = 1 := by
    rw [hJdef, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hss]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hbt : BlockTriangular b id := fun i j hij => hup i j hij
  haveI : Invertible b := b.invertibleOfIsUnitDet hdet
  have hinv : BlockTriangular b⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  have hright : bᵀ * (J * b.map (starRingEnd ℂ) * J) = 1 := by
    calc bᵀ * (J * b.map (starRingEnd ℂ) * J) = (bᵀ * J * b.map (starRingEnd ℂ)) * J := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have heq : J * b.map (starRingEnd ℂ) * J = (bᵀ)⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  rw [← Matrix.transpose_nonsing_inv] at heq
  have hoff : ∀ a c : Fin r, a < c → b a c = 0 := by
    intro a c hac
    have h1 := congrFun (congrFun heq a) c
    have h2 : (b⁻¹)ᵀ a c = 0 := by
      rw [transpose_apply]; exact hinv hac
    rw [h2, hJdef, mul_diagonal, diagonal_mul] at h1
    simp only [map_apply] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have hsc : (s c : ℂ) ≠ 0 := by rcases hs c with h | h <;> simp [h]
    have : (starRingEnd ℂ) (b a c) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hsa
        · exact h
      · exact absurd h hsc
    simpa using this
  have hdiag : ∀ a c : Fin r, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hoff a c h
    · exact hup a c h
  refine ⟨hdiag, fun a => ?_⟩
  have h1 := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · have hJaa : J a a = (s a : ℂ) := by simp [hJdef]
    rw [mul_diagonal, transpose_apply, map_apply, hJaa] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have h2 : b a a * (starRingEnd ℂ) (b a a) = 1 := by
      have : (s a : ℂ) * (b a a * (starRingEnd ℂ) (b a a)) = (s a : ℂ) * 1 := by
        linear_combination h1
      exact mul_left_cancel₀ hsa this
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (b a a) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : 0 ≤ ‖b a a‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖b a a‖ - 1), sq_nonneg (‖b a a‖ + 1)]
  · intro k _ hk
    rw [mul_diagonal, transpose_apply, map_apply, hdiag k a hk]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodularStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  first | exact @GlobalTheory.upperTriangular_signForm_diagonal | exact GlobalTheory.upperTriangular_signForm_diagonal | (intros; apply GlobalTheory.upperTriangular_signForm_diagonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonal
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem torusDer_sum_angles (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ i.castSucc = φ ⟨i, by simp⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simp)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl fun i _ => h1 i]
    rw [add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun i => rfl)

theorem torusDer_hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (w b)) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem torusDer_conj_mulVec (Y : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => conj ((Y *ᵥ w) b)) = Y.map (starRingEnd ℂ) *ᵥ fun b => conj (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem torusDer_skew_of_mat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hK : Yᵀ * G.map τ + G.map τ * Y.map (starRingEnd ℂ) = 0) (u w : Fin r → ℂ) :
    hermC τ G (Y *ᵥ u) w + hermC τ G u (Y *ᵥ w) = 0 := by
  rw [torusDer_hermC_dot, torusDer_hermC_dot, torusDer_conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, hK, zero_mulVec, dotProduct_zero]

end GlobalTheory.TorusFrame

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

theorem skewHermitian_of_diagonal_imaginary_frame {r : ℕ} (G M Y : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s)
    (hYM : Y * M = M * diagonal d) :
    Yᵀ * G + G * Y.map (starRingEnd ℂ) = 0 := by
  have e1 : Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = diagonal d * diagonal s := by
    calc Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = (Y * M)ᵀ * G * M.map (starRingEnd ℂ) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal s := by
          rw [hYM, transpose_mul, diagonal_transpose, ← hJ]; simp only [Matrix.mul_assoc]
  have e2 : Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) =
      diagonal s * (diagonal d).map (starRingEnd ℂ) := by
    calc Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = Mᵀ * G * (Y * M).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal s * (diagonal d).map (starRingEnd ℂ) := by
          rw [hYM, Matrix.map_mul, ← hJ]; simp only [Matrix.mul_assoc]
  have h2 : Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2]
    ext a b
    by_cases h : a = b
    · subst h; simp [diagonal_apply, hd]; ring
    · simp [diagonal_apply, h]
  have hL : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have hR : M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Yᵀ * G + G * Y.map (starRingEnd ℂ)
      = ((M⁻¹)ᵀ * Mᵀ) * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ)) := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    _ = (M⁻¹)ᵀ * (Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ)) *
          (M⁻¹).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

theorem torusDer_skew_diag {r : ℕ} (G M : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s) :
    (M * diagonal d * M⁻¹)ᵀ * G + G * (M * diagonal d * M⁻¹).map (starRingEnd ℂ) = 0 :=
  skewHermitian_of_diagonal_imaginary_frame G M _ hu d s hd hJ (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one])

theorem torusDer_mem_realLie_and_inFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧
      ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  intro E _ _ _ r X x hx θ
  have key : ∀ τ : X.Ψ, Matrix.of (torusDer x θ τ) =
      mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ := fun τ => rfl
  refine ⟨?_, fun τ a b => ?_⟩
  · intro τ
    have hu := isUnit_det_of_isOrth hx τ
    refine ⟨?_, fun u w => ?_⟩
    · rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, trace_diagonal,
        ← Finset.mul_sum, ← ofReal_sum, torusDer_sum_angles, ofReal_zero, mul_zero]
    · rw [key]
      refine torusDer_skew_of_mat τ.1 X.Gm _ ?_ u w
      refine torusDer_skew_diag _ _ hu _ (fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => ?_) ?_
      · simp
      · rw [← gram_eq]; exact hx τ
  · have hu := isUnit_det_of_isOrth hx τ
    unfold inFrame
    rw [key, show (mat x τ)⁻¹ * (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) * mat x τ =
        ((mat x τ)⁻¹ * mat x τ) * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * ((mat x τ)⁻¹ * mat x τ) by
        simp only [Matrix.mul_assoc], nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one, diagonal_apply]

end GlobalTheory.TorusFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonalStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  first | exact @GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | exact GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame | (intros; apply GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitary
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TorusFrame

theorem sum_angles {r : ℕ} (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ (Fin.castSucc i) = φ ⟨i, by simpa using i.isLt⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simpa using i.isLt)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl (fun i _ => h1 i)]
    simp

theorem hermC_eq_dot {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  simp only [hermC, dotProduct, mulVec, map_apply, Finset.mul_sum, mul_assoc]

theorem conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => (starRingEnd ℂ) ((M *ᵥ w) b)) = M.map (starRingEnd ℂ) *ᵥ fun b => (starRingEnd ℂ) (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem hermC_mulVec {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map (starRingEnd ℂ)) *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  rw [hermC_eq_dot, conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_phase {r : ℕ} (φ : Fin (r - 1) → ℝ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).det = 1 := by
  rw [det_diagonal, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_angles]
  simp

theorem phase_gram {r : ℕ} (φ : Fin (r - 1) → ℝ) (s : Fin r → ℂ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ))))ᵀ * diagonal s *
      (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).map (starRingEnd ℂ) = diagonal s := by
  rw [diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_conj, mul_comm (Complex.exp _) (s a), mul_assoc, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem torusGL_mem_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  intro E _ _ _ r X x hx θ
  intro τ
  have hu := isUnit_det_of_isOrth hx τ
  rw [torusGL_val]
  refine ⟨?_, fun u w => ?_⟩
  · rw [det_mul, det_mul, det_phase, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hu]
  · rw [hermC_mulVec, hermC_eq_dot]
    congr 2
    have hG := hx τ
    rw [gram_eq] at hG
    have h1 : (mat x τ)⁻¹ᵀ * (mat x τ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (mat x τ).map (starRingEnd ℂ) * ((mat x τ)⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGτ : X.Gm.map τ.1 = (mat x τ)⁻¹ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        ((mat x τ)⁻¹).map (starRingEnd ℂ) := by
      rw [Matrix.mul_assoc _ _ ((mat x τ)⁻¹.map _), Matrix.mul_assoc _ ((mat x τ).map _), h2, Matrix.mul_one,
        ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hG] at hGτ
    simp only [transpose_mul, Matrix.map_mul]
    rw [hGτ]
    have h1' : (mat x τ)ᵀ * (mat x τ)⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h2' : ((mat x τ)⁻¹).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have key := fun (Q : Matrix (Fin r) (Fin r) ℂ) =>
      (show (diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ)))ᵀ *
          ((diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          ((diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).map (starRingEnd ℂ) * Q)) =
          (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * Q by
        simp only [← Matrix.mul_assoc, phase_gram])
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat x τ)ᵀ, h1', Matrix.one_mul, ← Matrix.mul_assoc ((mat x τ)⁻¹.map _), h2',
      Matrix.one_mul, key]

end GlobalTheory.TorusFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitaryStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  first | exact @GlobalTheory.TorusFrame.torusGL_mem_realSU | exact GlobalTheory.TorusFrame.torusGL_mem_realSU | (intros; apply GlobalTheory.TorusFrame.torusGL_mem_realSU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZero
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZeroStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r), HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  first | exact @GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | exact GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero | (intros; apply GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFra
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section

namespace GlobalTheory.TorusFrame

theorem gram_mul_of_preserves {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M x : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * x) = ReciprocityTheory.ChartRestriction.G.FD.gram τ G x := by
  have hc (a : Fin r) : ReciprocityTheory.ChartRestriction.G.FD.col (M * x) a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col x a := by
    ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply, hc, hM]

theorem torus_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  intro E _ _ _ r X x hx
  refine ⟨fun θ => ⟨torusGL hx θ, GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary E r X x hx θ⟩, torusDer x, ?_, ?_, ?_, ?_, fun θ => GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal E r X x hx θ, ?_⟩
  · intro θ; funext τ
    show ((mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ) = (mat x τ * mat (phaseFrame θ) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]; rfl
  · intro θ θ'
    refine Subtype.ext (funext fun τ => ?_)
    have hp : phaseU ((θ + θ') τ) = phaseU (θ τ) * phaseU (θ' τ) := by
      refine Units.ext ?_
      simp only [phaseU, Units.val_mul, diagonal_mul_diagonal, Pi.add_apply, angles_add, Complex.ofReal_add,
        mul_add, Complex.exp_add]
    simp only [Subgroup.coe_mul, Pi.mul_apply, torusGL, hp]
    group
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    have hph : Continuous fun φ : Fin (r - 1) → ℝ => phaseU φ := by
      refine Units.continuous_iff.2 ⟨Continuous.matrix_diagonal (continuous_pi fun a => ?_),
        Continuous.matrix_diagonal (continuous_pi fun a => ?_)⟩
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a)))
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a))).neg
    exact (continuous_const.mul (hph.comp (continuous_apply τ))).mul continuous_const
  · exact GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero E r X.Ψ x
  · rintro g ⟨b, hb, hgb⟩
    have hgx (τ : X.Ψ) : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat b τ :=
      congrFun hgb τ
    have hdiag (τ : X.Ψ) := GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular r (mat b τ) (fun a => sgn X.p0 a)
      (fun a => by unfold sgn; split_ifs <;> simp) (isUnit_iff_ne_zero.2 (hb τ).1) (fun a c h => (hb τ).2 a c h) (by
        have h1 := gram_mul_of_preserves τ.1 X.Gm _ (mat x τ) ((g.2 τ).2)
        have hJ := hx τ
        rw [gram_eq] at hJ
        rw [hgx τ, gram_eq, gram_eq, transpose_mul, Matrix.map_mul] at h1
        rw [← hJ]; refine Eq.trans ?_ h1; simp only [Matrix.mul_assoc])
    have hbd (τ : X.Ψ) : mat b τ = diagonal fun a => mat b τ a a := by
      ext a c; by_cases h : a = c
      · subst h; simp
      · simp [diagonal_apply_ne _ h, (hdiag τ).1 a c h]
    have hdet (τ : X.Ψ) : ∏ a, mat b τ a a = 1 := by
      have h := congrArg Matrix.det (hgx τ)
      rw [det_mul, det_mul, (g.2 τ).1, one_mul, hbd τ, det_diagonal] at h
      exact (mul_left_cancel₀ (isUnit_det_of_isOrth hx τ).ne_zero (h.symm.trans (mul_one _).symm))
    choose φ hφ using fun τ : X.Ψ => GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one r (fun a => mat b τ a a) (hdiag τ).2 (hdet τ)
    refine ⟨φ, Subtype.ext (funext fun τ => Units.ext ?_)⟩
    show ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) * (mat x τ)⁻¹
    have hD : (diagonal fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) = mat b τ := by
      rw [hbd τ]; congr 1; funext a; exact hφ τ a
    rw [hD, ← hgx τ, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]

end GlobalTheory.TorusFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFraStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  first | exact @GlobalTheory.TorusFrame.torus_param | exact GlobalTheory.TorusFrame.torus_param | (intros; apply GlobalTheory.TorusFrame.torus_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentity
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.SUVol.DensChart

open scoped Pointwise

theorem mem_grpBall_iff_norm {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) {ε : ℝ}
    (hε : 0 < ε) (g : H) :
    g ∈ grpBall H ε ↔ ‖(fun τ i j => ((((g : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) i j) - (fun (_ : ι) i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j)‖ < ε := by
  rw [pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem tanBall_eq_ball {ι : Type} [Fintype ι] {r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tanBall ι r ε = Metric.ball 0 ε := by
  ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem density_at_one : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  intro ι _ r H _ μ W _ _ _ _ _ lam _ Q D h a ρ hD hQ0 hDi hon hh ha0 hat hρ hμ
  set f : W → (ι → Fin r → Fin r → ℂ) := fun w τ i j =>
    ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf
  set one : ι → Fin r → Fin r → ℂ := fun _ i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hone
  have hf0 : f 0 = one := by simp [hf, hone, hQ0]
  have hD' : HasStrictFDerivAt f D 0 := hD
  obtain ⟨K, -, hK⟩ := (D : W →ₗ[ℝ] (ι → Fin r → Fin r → ℂ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hDi)
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hnorm : ∀ w, ‖w‖ ≤ K' * ‖D w‖ := by
    intro w
    have h1 := hK.le_mul_dist w 0
    simp only [dist_zero_right, map_zero] at h1
    calc ‖w‖ ≤ K * ‖D w‖ := h1
      _ ≤ K' * ‖D w‖ := by gcongr; linarith
  have hcw : ∀ c : ℝ, 0 ≤ c → ∀ w, c / K' * ‖w‖ ≤ c * ‖D w‖ := by
    intro c hc w
    calc c / K' * ‖w‖ ≤ c / K' * (K' * ‖D w‖) := by gcongr; exact hnorm w
      _ = c * ‖D w‖ := by field_simp
  have approx : ∀ κ : ℝ, 0 < κ → ∃ δ > 0, ∀ w : W, ‖w‖ < δ → ‖f w - one - D w‖ ≤ κ * ‖w‖ := by
    intro κ hκ
    have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD'.hasFDerivAt).def hκ
    obtain ⟨δ, hδ, hh'⟩ := Metric.eventually_nhds_iff.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hh' (y := w) (by rwa [dist_zero_right])
    simpa [hf0] using this
  set V : ℝ → ℝ≥0∞ := fun ε => lam (D ⁻¹' Metric.ball 0 ε) with hVdef
  set S : ℝ → Set W := fun ε => D ⁻¹' Metric.ball 0 ε ∩ Metric.ball 0 ρ with hSdef
  set F : ℝ → ℝ≥0∞ := fun ε => μ (Q '' S ε) with hFdef
  have hV0 : ∀ ε : ℝ, 0 < ε → V ε ≠ 0 := fun ε hε =>
    (Metric.isOpen_ball.preimage D.continuous).measure_ne_zero lam ⟨0, by simp [hε]⟩
  have hVt : ∀ ε : ℝ, V ε ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := lam) (x := 0) (r := K' * ε)).ne
      (measure_mono fun w hw => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ ≤ K' * ε := by gcongr
  have hVhom : ∀ t ε : ℝ, 0 < t → 0 < ε → V (t * ε) = ENNReal.ofReal (t ^ Module.finrank ℝ W) * V ε := by
    intro t ε ht _
    have hs : D ⁻¹' Metric.ball 0 (t * ε) = t • (D ⁻¹' Metric.ball 0 ε) := by
      ext w
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
      simp only [Set.mem_preimage, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht]
      rw [inv_mul_lt_iff₀ ht]
    simp only [hVdef]
    rw [hs, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]
  have hSmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurableSet_ball.preimage D.measurable).inter measurableSet_ball
  have hSeq : ∀ ε : ℝ, ε < ρ / K' → S ε = D ⁻¹' Metric.ball 0 ε := by
    intro ε hε
    refine Set.inter_eq_left.2 fun w hw => ?_
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ < K' * (ρ / K') := by gcongr; linarith [norm_nonneg (D w)]
      _ = ρ := by field_simp
  have hFint : ∀ ε : ℝ, F ε = ∫⁻ w in S ε, h w ∂lam := fun ε =>
    hμ (S ε) (hSmeas ε) Set.inter_subset_right
  have hF : Tendsto (fun ε => F ε / V ε) (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨a', hb', ha'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (lt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : a' * V ε ≤ F ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc b < a' := hb'
        _ = a' * V ε / V ε := (ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)).symm
        _ ≤ F ε / V ε := ENNReal.div_le_div_right hle _
    · obtain ⟨a', ha', hb'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (gt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : F ε ≤ a' * V ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc F ε / V ε ≤ a' * V ε / V ε := ENNReal.div_le_div_right hle _
        _ = a' := ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)
        _ < b := hb'
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (t⁻¹ * ε) ≤ μ (grpBall H ε) ∧ μ (grpBall H ε) ≤ F (t * ε) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    obtain ⟨δ1, hδ1, H1⟩ := approx ((t - 1) / K') (div_pos (by linarith) hK'0)
    obtain ⟨δ2, hδ2, H2⟩ := approx ((1 - t⁻¹) / K') (div_pos (by linarith) hK'0)
    obtain ⟨ε0, hε0, hon0⟩ := hon (min ρ δ2) (lt_min hρ hδ2)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hε0 (lt_min (div_pos hδ1 hK'0) (div_pos hρ hK'0)))]
      with ε hε
    obtain ⟨hεp, hε1⟩ := hε
    simp only [lt_min_iff] at hε1
    obtain ⟨hεe, hεd, hερ⟩ := hε1
    constructor
    · refine measure_mono ?_
      rintro _ ⟨w, ⟨hw1, -⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff] at hw1
      rw [mem_grpBall_iff_norm H hεp]
      change ‖f w - one‖ < ε
      have hDw : ‖D w‖ < ε := by
        calc ‖D w‖ < t⁻¹ * ε := hw1
          _ < 1 * ε := by gcongr
          _ = ε := one_mul ε
      have hw : ‖w‖ < δ1 := by
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δ1 / K') := by gcongr; linarith
          _ = δ1 := by field_simp
      have e1 := H1 w hw
      have e2 := hcw (t - 1) (by linarith) w
      have e3 : ‖f w - one‖ ≤ ‖D w‖ + ‖f w - one - D w‖ := by
        calc ‖f w - one‖ = ‖D w + (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have e4 : t * ‖D w‖ < ε := by
        calc t * ‖D w‖ < t * (t⁻¹ * ε) := by gcongr
          _ = ε := by field_simp
      nlinarith
    · refine measure_mono fun g hg => ?_
      have hg0 : g ∈ grpBall H ε0 := fun τ i j => (hg τ i j).trans hεe
      obtain ⟨w, hw, rfl⟩ := hon0 g hg0
      rw [lt_min_iff] at hw
      rw [mem_grpBall_iff_norm H hεp] at hg
      change ‖f w - one‖ < ε at hg
      refine ⟨w, ⟨?_, mem_ball_zero_iff.2 hw.1⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have e1 := H2 w hw.2
      have e2 := hcw (1 - t⁻¹) (by linarith) w
      have e3 : ‖D w‖ ≤ ‖f w - one‖ + ‖f w - one - D w‖ := by
        calc ‖D w‖ = ‖(f w - one) - (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e4 : t⁻¹ * ‖D w‖ < ε := by linarith
      calc ‖D w‖ = t * (t⁻¹ * ‖D w‖) := by field_simp
        _ < t * ε := by gcongr
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze (F := F) (V := V)
    (A := fun ε => μ (grpBall H ε)) (n := Module.finrank ℝ W) hat hVhom hF hA
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  simp only [hVdef]
  rw [tanBall_eq_ball hε, Measure.map_apply D.measurable measurableSet_ball]

end GlobalTheory.SUVol.DensChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentityStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixGroup_chart_density_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  first | exact @GlobalTheory.SUVol.DensChart.density_at_one | exact GlobalTheory.SUVol.DensChart.density_at_one | (intros; apply GlobalTheory.SUVol.DensChart.density_at_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentity
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  intro ι _ r H W₁ W₂ _ _ _ _ σ t D₁ D₂ hσ ht h₁ h₂
  set f₁ : W₁ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₁
  set f₂ : W₂ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₂
  have e : (fun w : W₁ × W₂ => fun τ i j =>
      ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) =
      fun w τ i j => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j := by
    funext w τ i j
    simp [hf₁, hf₂, Matrix.mul_apply]
  have z₁ : ∀ τ i c, f₁ 0 τ i c = (1 : Matrix (Fin r) (Fin r) ℂ) i c := by
    intro τ i c; simp [hf₁, hσ]
  have z₂ : ∀ τ c j, f₂ 0 τ c j = (1 : Matrix (Fin r) (Fin r) ℂ) c j := by
    intro τ c j; simp [hf₂, ht]
  have g₁ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1)
      (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₁.comp (0 : W₁ × W₂) (hasStrictFDerivAt_fst (p := (0 : W₁ × W₂)))
  have g₂ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2)
      (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₂.comp (0 : W₁ × W₂) (hasStrictFDerivAt_snd (p := (0 : W₁ × W₂)))
  rw [e]
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun i =>
    hasStrictFDerivAt_pi'.2 fun j => ?_
  have a₁ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1 τ i c)
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.proj τ).comp (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₁ τ) i) c
  have a₂ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2 τ c j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj c).comp
        ((ContinuousLinearMap.proj τ).comp (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₂ τ) c) j
  have hs0 := HasStrictFDerivAt.sum (u := Finset.univ) (A := fun c (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j)
    (fun c _ => (a₁ c).mul (a₂ c))
  have ef : (fun w : W₁ × W₂ => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j) =
      ∑ c, (fun (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j) := by
    funext w
    simp [Finset.sum_apply]
  rw [ef]
  refine hs0.congr_fderiv ?_
  clear ef hs0 a₁ a₂ g₁ g₂ e
  clear_value f₁ f₂
  clear hf₁ hf₂ h₁ h₂ hσ ht σ t
  refine ContinuousLinearMap.ext fun w => ?_
  simp [z₁, z₂, Matrix.one_apply, Finset.sum_add_distrib, ite_mul]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentityStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  first | exact @GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | exact GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | (intros; apply GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaar
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.RiemConst

theorem riemHaar_eq_smul (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)]
    (ν : Measure (realSU X.Ψ X.Gm)) (hr : 1 ≤ r) (hx : IsOrth X x) (hν : ν.IsHaarMeasure)
    (hfib : ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x) :
    riemHaar X.Ψ X.Gm x = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  obtain ⟨hdc, hd0, hdet⟩ := GlobalTheory.T.chartDensity_continuousAt_zero_eq_one E r X x hx
  obtain ⟨hf, hnd⟩ := GlobalTheory.T.totallyRealDegree_and_chartDimension_eq E r X
  obtain ⟨σ, ρ, D₁, hρ, hσ0, hσc, hσB, hσD, hD₁⟩ := GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart E r X x hx
  obtain ⟨t, Dt, htx, htmul, htc, htD, hDt, hstab⟩ := GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame E r X x hx
  have ht0 : t 0 = 1 := by
    have h := congrArg (fun g => (t 0)⁻¹ * g) (htmul 0 0)
    simp only [add_zero, inv_mul_cancel, inv_mul_cancel_left] at h
    exact h.symm
  let D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    D₁.comp (ContinuousLinearMap.fst ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ)) +
      Dt.comp (ContinuousLinearMap.snd ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ))
  have hQD := GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity X.Ψ r (realSU X.Ψ X.Gm) (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ) σ t D₁ Dt hσ0 ht0 hσD htD
  have hspec : ∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧
      (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧
        ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ) := by
    intro w
    have hDw : D w = D₁ w.1 + Dt w.2 := rfl
    have e : ∀ τ, inFrame x (D w) τ = inFrame x (D₁ w.1) τ + inFrame x (Dt w.2) τ := by
      intro τ
      simp only [inFrame, hDw]
      rw [show Matrix.of ((D₁ w.1 + Dt w.2) τ) = Matrix.of (D₁ w.1 τ) + Matrix.of (Dt w.2 τ) from rfl,
        Matrix.mul_add, Matrix.add_mul]
    obtain ⟨h1, h2, h3⟩ := hD₁ w.1
    obtain ⟨h4, h5⟩ := hDt w.2
    refine ⟨?_, fun τ a b hab => ?_, fun τ a => ?_⟩
    · rw [hDw]; exact (realLie X.Ψ X.Gm).add_mem h1 h4
    · rw [e, Matrix.add_apply, h2 τ a b hab, h5, if_neg (ne_of_gt hab), add_zero]
    · rw [e, Matrix.add_apply, h3, h5, if_pos rfl, zero_add]
  obtain ⟨hDinj, hriem⟩ := GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue E r X x hr hx D hspec
  have hform := GlobalTheory.T.haar_specialUnitary_product_chart_formula E r X x ν σ t ρ hr hx hν hfib hρ hσc hσB htx htmul htc hstab
  have hsurj := GlobalTheory.T.specialUnitary_near_one_eq_chart_mul E r X x σ t ρ hx hρ hσ0 hσc hσB htx htmul htc hstab
  set m := (r - 1) * X.Ψ.card with hm
  set a : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi) ^ m) with ha
  have hpi : 0 < (2 * Real.pi) ^ m := by positivity
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have htend : Tendsto (fun w : ChartSp X => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) (𝓝 0) (𝓝 a) := by
    have h1 : ContinuousAt (fun w : ChartSp X => densF X x w.1) 0 :=
      ContinuousAt.comp (g := densF X x) (f := Prod.fst) (x := (0 : ChartSp X)) hdc continuous_fst.continuousAt
    have h2 := (ENNReal.continuous_ofReal.continuousAt).tendsto.comp ((h1.div_const ((2 * Real.pi) ^ m)).tendsto)
    rw [ha]
    simpa [Function.comp_def, hd0] using h2
  have hρ' : 0 < min ρ Real.pi := lt_min hρ Real.pi_pos
  have hQ0 : (fun w : ChartSp X => σ w.1 * t w.2) 0 = 1 := by simp [hσ0, ht0]
  haveI : (volume : Measure (X.Ψ → Fin (r - 1) → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ChartSp X)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (V (nd X))) (volume : Measure (X.Ψ → Fin (r - 1) → ℝ))
  have hlim := GlobalTheory.T.matrixGroup_chart_density_at_identity X.Ψ r (realSU X.Ψ X.Gm) ν (ChartSp X) volume (fun w => σ w.1 * t w.2) D
    (fun w => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) a (min ρ Real.pi) hQD hQ0 hDinj hsurj htend
    ha0 hatop hρ' hform
  obtain ⟨hRH, hRdens⟩ := GlobalTheory.SUVol.DensOne.tangentHaar_riemLie X.Ψ X.Gm X.Gm_det x hdet
  have hRH' : (riemHaar X.Ψ X.Gm x).IsHaarMeasure := hRH
  set k := (riemHaar X.Ψ X.Gm x).haarScalarFactor ν with hkdef
  have hk : riemHaar X.Ψ X.Gm x = k • ν := Measure.isMulLeftInvariant_eq_smul _ _
  set K := ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) with hKdef
  have hK0 : K ≠ 0 := by
    rw [hKdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast hr)
    positivity
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 ((k : ℝ≥0∞) * a * K⁻¹)) :=
    ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top))
      (Or.inr (ENNReal.inv_ne_top.2 hK0))
  unfold HasDensityOne at hRdens
  have h2 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 1) := by
    refine hRdens.congr fun ε => ?_
    rw [show tangentHaar (realSU X.Ψ X.Gm) (riemLie X.Ψ X.Gm x) = riemHaar X.Ψ X.Gm x from rfl, hk, hriem]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop)]
    ring
  have e := tendsto_nhds_unique h1 h2
  have hkval : (k : ℝ≥0∞) = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) := by
    have e' : (k : ℝ≥0∞) * (a * K⁻¹) = 1 := by rw [← mul_assoc]; exact e
    have hai : a⁻¹ = ENNReal.ofReal ((2 * Real.pi) ^ m) := by
      rw [ha, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [ENNReal.eq_inv_of_mul_eq_one_left e', ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), inv_inv, hai,
      hKdef, ← ENNReal.ofReal_mul hpi.le]
    congr 1
    rw [hf, hnd, hm]
    generalize r * (r - 1) / 2 = n1
    generalize r - 1 = n2
    ring
  rw [hk, ← hkval]
  ext s _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.RiemConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaarStatement
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → riemHaar X.Ψ X.Gm x = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  first | exact @GlobalTheory.RiemConst.riemHaar_eq_smul | exact GlobalTheory.RiemConst.riemHaar_eq_smul | (intros; apply GlobalTheory.RiemConst.riemHaar_eq_smul <;> assumption)
end
