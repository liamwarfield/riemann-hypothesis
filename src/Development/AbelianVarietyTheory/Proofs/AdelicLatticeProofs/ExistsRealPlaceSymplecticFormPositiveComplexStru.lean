module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StarTraceHerm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CartanTrace

theorem star_trace_herm {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (x y : Matrix (Fin m) (Fin n) ℂ) :
    star (A * yᴴ * B * x).trace = (A * xᴴ * B * y).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

open scoped MatrixOrder in
theorem trace_pos {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < (A * xᴴ * B * x).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  obtain ⟨D, hD, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hB.isStrictlyPositive
  have e : (star C * C * xᴴ * (star D * D) * x).trace = ((D * x * Cᴴ)ᴴ * (D * x * Cᴴ)).trace := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine lt_of_le_of_ne (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg ?_
  intro h
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h.symm
  apply hx
  have hC' : IsUnit Cᴴ := hC.star
  have hD' := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hC'' := (Matrix.isUnit_iff_isUnit_det _).1 hC'
  have : x = D⁻¹ * (D * x * Cᴴ) * Cᴴ⁻¹ := by
    rw [Matrix.mul_assoc D, Matrix.nonsing_inv_mul_cancel_left _ _ hD',
      Matrix.mul_nonsing_inv_cancel_right _ _ hC'']
  rw [this, h0]; simp

variable {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}

theorem adj_mul (h : IsCartanInv G s) : sᴴ * G = G * s := by
  have := congrArg (· * s) h.2.1
  simpa only [Matrix.mul_assoc, h.1, Matrix.mul_one] using this

theorem adj_sq (h : IsCartanInv G s) : sᴴ * sᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, h.1, Matrix.conjTranspose_one]

theorem herm (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : sᴴ * Gᴴ = sᴴ * G := by
    rw [← Matrix.conjTranspose_mul, adj_mul h]; exact h.2.2.isHermitian
  have := congrArg (sᴴ * ·) h1
  simpa only [← Matrix.mul_assoc, adj_sq h, Matrix.one_mul] using this

theorem inv_mul_adj (h : IsCartanInv G s) : G⁻¹ * sᴴ = (G * s)⁻¹ := by
  rw [← adj_mul h, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (adj_sq h)]

theorem form_cplxO {m n : ℕ} {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ}
    {ξ : ℂ} (hξ : ξ.re = 0) (hS : IsCartanInv GS sS) (hT : IsCartanInv GT sT)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re =
      ξ.im * ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x).trace.re := by
  have e : GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x =
      (-Complex.I) • ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x) := by
    rw [← inv_mul_adj hS, ← adj_mul hT]
    simp only [cplxO, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Complex.star_def, Complex.conj_I]
  rw [e, Matrix.trace_smul]
  simp [hξ]

theorem cplxO_pos : ∀ (m n : ℕ) (GS sS : Matrix (Fin n) (Fin n) ℂ) (GT sT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ), ξ.re = 0 → 0 < ξ.im → IsCartanInv GS sS → IsCartanInv GT sT → (∀ x : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * xᴴ * GT * x).trace).re = 0) ∧ (∀ x : Matrix (Fin m) (Fin n) ℂ, cplxO sS sT (cplxO sS sT x) = -x) ∧ (∀ x y : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re = (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * y).trace).re) ∧ ∀ x : Matrix (Fin m) (Fin n) ℂ, x ≠ 0 → 0 < (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * x).trace).re := by
  intro m n GS sS GT sT ξ h0 h1 hS hT
  refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · have hi : GS⁻¹ᴴ = GS⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, herm hS]
    have := congrArg Complex.im (star_trace_herm hi (herm hT) x x)
    have h2 : (GS⁻¹ * xᴴ * GT * x).trace.im = 0 := by
      rw [Complex.star_def, Complex.conj_im] at this; linarith
    simp [h0, h2]
  · simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT.1, Matrix.one_mul, Matrix.mul_assoc, hS.1]
    simp
  · rw [form_cplxO h0 hS hT, form_cplxO h0 hS hT,
      ← star_trace_herm hS.2.2.inv.isHermitian hT.2.2.isHermitian x y]
    simp
  · rw [form_cplxO h0 hS hT]
    exact mul_pos h1 (Complex.pos_iff.1 (trace_pos hS.2.2.inv hT.2.2 x hx)).1

end GlobalTheory.CartanTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrientedRealForm

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem map_inv_of_det_ne {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map φ)⁻¹ = G⁻¹.map φ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.2 h), Matrix.map_one _ φ.map_zero φ.map_one]

theorem trace_eq_sum {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ e, ∑ d, P a b * starRingEnd ℂ (y e b) * Q e d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  rfl

variable {D : D7}

theorem formAt_eq (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ x y =
      2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace).re := by
  rw [trace_eq_sum]
  unfold formAt gramAt
  rw [map_inv_of_det_ne _ _ (gram_det_ne S)]
  rfl

theorem realPlace_imaginaryGenerator_re_eq_zero (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  have h := tauE_star τ D.host.xi0
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg] at h
  have h2 := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at h2
  linarith

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  unfold cplxO
  rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun z := fun τ => cplxO (sS τ) (sT τ) (z τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem exists_real_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  intro D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ) (tauE D τ D.host.xi0)
    (realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ (z : RW T S) τ, jO S T sS sT z τ = cplxO (sS τ) (sT τ) (z τ) := fun _ _ => rfl
  refine ⟨omO S T, jO S T sS sT, fun x y hy => ?_, hJ, omO_self h, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [← psi_symplOH h hψ, h.iota_pi (V := T) (W := S) hy]
  · funext τ
    exact (key τ).2.1 (v τ)
  · rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (formAt_eq S T τ _ _).trans (Eq.trans ?_ (formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  · rw [hom]
    have hp : ∀ τ, v τ ≠ 0 → 0 < formAt S T τ (v τ) (jO S T sS sT v τ) := fun τ h0 =>
      lt_of_lt_of_eq (mul_pos two_pos ((key τ).2.2.2 (v τ) h0)) (formAt_eq S T τ _ _).symm
    obtain ⟨τ₀, h₀⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, hp τ₀ h₀⟩
    by_cases h0 : v τ = 0
    · rw [h0]
      simp [formAt]
    · exact (hp τ h0).le

end GlobalTheory.OrientedRealForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStruStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realPlace_symplecticForm_positiveComplexStructure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  first | exact @GlobalTheory.OrientedRealForm.exists_real_form | exact GlobalTheory.OrientedRealForm.exists_real_form | (intros; apply GlobalTheory.OrientedRealForm.exists_real_form <;> assumption)
end
