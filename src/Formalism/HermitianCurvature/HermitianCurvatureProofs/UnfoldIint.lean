module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OoConvOf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadInner1
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormTwoSidedTranslateGrowthBound
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEnormComposition
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousSandwichedProduct
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNSandwich
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem coef_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {z Y z' : Mx k r}
    (hz : z ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ z w, σ Y (σ z' w)⟫_ℂ = ⟪w, σ (z⁻¹ * Y * z') w⟫_ℂ := by
  have hzi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hz
  have hiso := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).2 z hz
  have hM : z⁻¹ * Y * z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hzi.1 hY) hz'
  have h1 : σ Y (σ z' w) = σ z (σ (z⁻¹ * Y * z') w) := by
    have e1 : σ (Y * z') = (σ Y).comp (σ z') := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hY hz'
    have e2 : σ (z * (z⁻¹ * Y * z')) = (σ z).comp (σ (z⁻¹ * Y * z')) :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hz hM
    have e3 : z * (z⁻¹ * Y * z') = Y * z' := by
      rw [← mul_assoc, ← mul_assoc, hzi.2.1, one_mul]
    rw [e3] at e2
    have h2 := congrArg (fun T => T w) (e1.symm.trans e2)
    simpa using h2
  rw [h1]
  exact (⟨(σ z).toLinearMap, hiso⟩ : H →ₗᵢ[ℂ] H).inner_map_map w _

theorem gN_sandwich (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by
  have hN := hNI k r
  have hxi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hx
  have hyi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hxi.1 hA) hy
  have hm1 := (hN.2 _ hM).2
  have ha1 := (hN.2 _ hA).2
  have hx1 := (hN.2 _ hx).2
  have hy1 := (hN.2 _ hy).2
  have hyinv := (hN.2 _ hy).1
  have hAeq : x * (x⁻¹ * A * y) * y⁻¹ = A := by
    rw [show x * (x⁻¹ * A * y) * y⁻¹ = (x * x⁻¹) * A * (y * y⁻¹) by simp only [mul_assoc],
      hxi.2.1, hyi.2.1, one_mul, mul_one]
  have hle : B.gN A ≤ (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by
    calc B.gN A = B.gN (x * (x⁻¹ * A * y) * y⁻¹) := by rw [hAeq]
      _ ≤ B.gN (x * (x⁻¹ * A * y)) * B.gN y⁻¹ := hN.1 _ _
      _ ≤ B.gN x * B.gN (x⁻¹ * A * y) * B.gN y⁻¹ :=
          mul_le_mul_of_nonneg_right (hN.1 _ _) (by rw [hyinv]; linarith)
      _ = (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by rw [hyinv]; ring
  have hp : 0 < B.gN x * B.gN y := mul_pos (by linarith) (by linarith)
  have hmb : 0 < B.gN (x⁻¹ * A * y) ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hab : 0 < B.gN A ^ b := Real.rpow_pos_of_pos (by linarith) b
  have key : B.gN A ^ b ≤ (B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hle hb
  rw [Real.rpow_neg (show (0:ℝ) ≤ B.gN (x⁻¹ * A * y) by linarith),
    Real.rpow_neg (show (0:ℝ) ≤ B.gN A by linarith)]
  calc (B.gN (x⁻¹ * A * y) ^ b)⁻¹
        = (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * B.gN A ^ b * (B.gN A ^ b)⁻¹ := by
          exact (mul_inv_cancel_right₀ hab.ne' _).symm
    _ ≤ (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * ((B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b) *
          (B.gN A ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hmb.le))
          (inv_nonneg.2 hab.le)
    _ = (B.gN x * B.gN y) ^ b * (B.gN A ^ b)⁻¹ := by
        rw [mul_comm ((B.gN x * B.gN y) ^ b) (B.gN (x⁻¹ * A * y) ^ b), inv_mul_cancel_left₀ hmb.ne']

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem lintegral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α} {f : α → α}
    (hμ : μ.map f = μ) {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (f x) ∂μ = ∫⁻ x, G x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · conv_rhs => rw [← hμ]
    rw [lintegral_map' hG.aemeasurable hf]
  · by_cases h0 : μ = 0
    · simp [h0]
    · haveI : Nonempty α := Measure.nonempty_of_not_aemeasurable hf
      have hd : μ = Measure.dirac (Classical.ofNonempty : α) :=
        hμ.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hf h0)
      rw [hd] at hf
      exact (hf aemeasurable_dirac).elim

theorem lint_lmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_left {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1

  have step1 : (fun x => ∫⁻ y, F (fun i j => (h0 * n0 * (Matrix.of x * Matrix.of y)) i j) ∂μN) =ᵐ[μW]
      fun x => ∫⁻ y, F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j) ∂μN := by
    filter_upwards [hae] with x hx
    obtain ⟨hxi, hx1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hx
    have hm : (Matrix.of x)⁻¹ * n0 * Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
      have h1 := (Formalism.QuantumDeterminants.uWNormal k r z hz _ hxi n0 hn0).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse hx1)] at h1
    have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (h0 * Matrix.of x * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of x * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, h0 * n0 * (Matrix.of x * Matrix.of y) =
        h0 * Matrix.of x * Matrix.of (Formalism.QuantumDeterminants.lmulM ((Matrix.of x)⁻¹ * n0 * Matrix.of x) y) := by
      intro y
      show _ = h0 * Matrix.of x * ((Matrix.of x)⁻¹ * n0 * Matrix.of x * Matrix.of y)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.of x) (Matrix.of x)⁻¹, hx1, Matrix.one_mul]
    simp_rw [e1]
    exact lint_lmul (hN.2.2.2 _ hm) hG
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable,
    MeasureTheory.lintegral_congr_ae step1,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e2 : ∀ x : Formalism.QuantumDeterminants.Mt k r, h0 * Matrix.of x * Matrix.of y =
      Matrix.of (Formalism.QuantumDeterminants.lmulM h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e2]
  exact lint_lmul (hW.2.2.2 h0 hh0) hG

theorem lint_rmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (B.rmulF a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (B.rmulF a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem lint_conj {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.conjM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.conjM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_right {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  obtain ⟨hi, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh0
  have hinv : h0⁻¹⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse h1)
  have hconj : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN _ hi
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)

  have inner : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ y, F (fun i j => (Matrix.of x * Matrix.of y * (h0 * n0)) i j) ∂μN =
        ∫⁻ y, F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j) ∂μN := by
    intro x
    have hG1 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have hG2 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * Matrix.of y * (h0 * n0) =
        Matrix.of x * h0 * Matrix.of (Formalism.QuantumDeterminants.conjM h0⁻¹ y) * n0 := by
      intro y
      show _ = Matrix.of x * h0 * (h0⁻¹ * Matrix.of y * h0⁻¹⁻¹) * n0
      rw [hinv]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h0 h0⁻¹, h1, Matrix.one_mul]
    have e2 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y * n0 =
        Matrix.of x * h0 * Matrix.of (B.rmulF n0 y) := by
      intro y
      show _ = Matrix.of x * h0 * (Matrix.of y * n0)
      simp only [Matrix.mul_assoc]
    simp_rw [e1]
    rw [lint_conj hconj hG1]
    simp_rw [e2]
    exact lint_rmul (hN.right n0 hn0) hG2
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable]
  simp_rw [inner]
  rw [MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG3 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e3 : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y =
      Matrix.of (B.rmulF h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e3]
  exact lint_rmul (hW.right h0 hh0) hG3

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

def abelian₂ (e0 : Mx k r → ℂ) (γ : Mx k r) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (x y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
    Matrix.of y)‖ₑ ∂μq ∂μp

def Lam1 (e0 : Mx k r → ℂ) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x y : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂μp

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) :
    Measurable (fun t => (fun i j => ((Matrix.of (f t))⁻¹ : Mx k r) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  (B2x1.invM_meas (k := k) (r := r)).comp hf

theorem measurable_enorm_composition {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) :=
  ((he0.comp mt_cont).measurable.comp hf).enorm

theorem meas_hn {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) :
    Measurable (fun t => (fun i j => (Matrix.of (f t).1 * Matrix.of (f t).2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_matmul hf.fst hf.snd

theorem meas_lam_int {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by
  have mγ : Measurable (fun _ : α => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) mγ)
    (meas_inv (meas_hn hQ))) hY
  exact measurable_enorm_composition he0 M

theorem measurable_lambda_integrand {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) *
      Matrix.of (Y t))‖ₑ) := by
  have M := meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) hY
  exact measurable_enorm_composition he0 M

theorem meas_lam {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] [SFinite μq] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => abelian₂ e0 γ μp μq t.1 t.2) := by
  unfold abelian₂
  have m4 := meas_lam_int he0 γ (α := ((Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (measurable_fst.fst.fst) (measurable_fst.fst.snd) measurable_fst.snd measurable_snd
  have m3 := m4.lintegral_prod_right' (ν := μq)
  exact m3.lintegral_prod_right' (ν := μp)

theorem measurable_lambda_integral {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Lam1 e0 μp t.1 t.2) := by
  unfold Lam1
  have m3 := measurable_lambda_integrand he0 (α := (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) (measurable_fst.fst) (measurable_fst.snd) measurable_snd
  exact m3.lintegral_prod_right' (ν := μp)

theorem meas_const_mt (c : Formalism.QuantumDeterminants.Mt k r) {α : Type*} [MeasurableSpace α] :
    Measurable (fun _ : α => c) := measurable_const

theorem lam_left {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μq]
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ (μW.prod μN) μq (fun i j => (h0 * n0 * Matrix.of x) i j) y = abelian₂ e0 γ (μW.prod μN) μq x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq with hF
  have hFm : Measurable F := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
    have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt x'))
      measurable_fst) mγ) (meas_inv (meas_hn measurable_snd))) (meas_const_mt y)
    exact (measurable_enorm_composition he0 M).lintegral_prod_right'
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold abelian₂
  calc ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lam_right {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ μp (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = abelian₂ e0 γ μp (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, hSS, -⟩ := MatrixMultiplicationContinuity.uh_inv hS
  unfold abelian₂
  apply lintegral_congr
  intro p
  set y' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of y) i j with hy'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of m)⁻¹ * Matrix.of y')‖ₑ with hF
  have hFm : Measurable F := by
    have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    have M := meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt y')
    exact measurable_enorm_composition he0 M
  have hpl := param_left hW hN hz hh0 hn0 hFm
  calc ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y')‖ₑ ∂(μW.prod μN)
      = ∫⁻ q, F (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ q, F (fun i j => (h0 * n0 * (Matrix.of q.1 * Matrix.of q.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hSS' := (MatrixMultiplicationContinuity.uh_inv hS).2.2
        have hmat : ∀ (Z Q : Mx k r), Z * (Matrix.of (fun i j => (h0 * n0 * Q) i j : Formalism.QuantumDeterminants.Mt k r))⁻¹ *
            Matrix.of y' = Z * Q⁻¹ * Matrix.of y := by
          intro Z Q
          show Z * (h0 * n0 * Q)⁻¹ * (h0 * n0 * Matrix.of y) = Z * Q⁻¹ * Matrix.of y
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS',
            Matrix.one_mul, ← Matrix.mul_assoc]
        simp only [hF, hmat]

theorem lambda_left_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) (fun i j => (h0 * n0 * Matrix.of x) i j) y = Lam1 e0 (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x')) measurable_id) (meas_const_mt y))
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lambda_right_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = Lam1 e0 (μW.prod μN) x y := by
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x)) measurable_id) (meas_const_mt y))
  have hpr := param_right hW hN hz hT hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) *
        Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) := by
        have hmat : ∀ P : Mx k r, (Matrix.of x)⁻¹ * P *
            Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * Matrix.of (fun i j => (P * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r) * Matrix.of y := by
          intro P
          show (Matrix.of x)⁻¹ * P * (h0 * n0 * Matrix.of y) = (Matrix.of x)⁻¹ * (P * (h0 * n0)) * Matrix.of y
          simp only [Matrix.mul_assoc]
        simp only [hF, hmat]
    _ = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := hpr
    _ = _ := rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem norm_two_sided_translate_growth_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖e0 (x⁻¹ * A * y)‖ₑ ≤ ENNReal.ofReal (|C0| * (B.gN x * B.gN y) ^ b) * ‖B.gN A ^ (-b)‖ₑ := by
  have hxi := (MatrixMultiplicationContinuity.uh_inv hx).1
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hxi hA) hy
  have h1 : 1 ≤ B.gN (x⁻¹ * A * y) := ((hNI k r).2 _ hM).2
  have hAp : 0 ≤ B.gN A ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hxy : 0 ≤ (B.gN x * B.gN y) ^ b := Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  rw [Real.enorm_eq_ofReal hAp, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hxy), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖e0 (x⁻¹ * A * y)‖ ≤ C0 * B.gN (x⁻¹ * A * y) ^ (-a) := hb0e _ hM
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ |C0| * ((B.gN x * B.gN y) ^ b * B.gN A ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_sandwich hNI hx hA hy hb0) (abs_nonneg _)
    _ = |C0| * (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by ring

theorem lam_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hq : ∀ᵐ q ∂μq, Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    abelian₂ e0 γ μp μq x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-b)‖ₑ ∂μq ∂μp := by
  unfold abelian₂
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hq] with q hqq
  have hQi := (MatrixMultiplicationContinuity.uh_inv hqq).1
  have hA : (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hpp hγ) hQi
  have e : (Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
      Matrix.of y = (Matrix.of x)⁻¹ * ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) *
      Matrix.of y := by simp only [Matrix.mul_assoc]
  rw [e]
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hA hy

theorem lambda_integral_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Lam1 e0 μp x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)‖ₑ ∂μp := by
  unfold Lam1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hpp hy

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem hphi_meas : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_hn measurable_id

theorem quad_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μW μN μW' : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS2 : muSof μW' μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
      ∂(muSof μW' μN) ∂(muSof μW μN) = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hae2 : ∀ᵐ s ∂(muSof μW' μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS2
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t.1 * γ * (Matrix.of t.2)⁻¹ * Matrix.of zz')‖ₑ) := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    exact measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz))
      measurable_fst) mγ) (meas_inv measurable_snd)) (meas_const_mt zz'))
  calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
        ∂(muSof μW' μN) ∂(muSof μW μN)
      = ∫⁻ s, ∫⁻ s', ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * γ * (Matrix.of s')⁻¹ * Matrix.of zz')‖ₑ
          ∂(muSof μW' μN) ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        apply lintegral_congr_ae
        filter_upwards [hae2] with s' hs'
        have hY : Matrix.of s * γ * (Matrix.of s')⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul hs hγ) (MatrixMultiplicationContinuity.uh_inv hs').1
        have hM : (Matrix.of zz)⁻¹ * (Matrix.of s * γ * (Matrix.of s')⁻¹) * Matrix.of zz' ∈
            Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hY) hz'
        rw [coef_eq hds hz hY hz', ← hee0 _ hM]
        simp only [Matrix.mul_assoc]
    _ = ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of zz)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
          (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of zz')‖ₑ ∂(μW'.prod μN) ∂(μW.prod μN) := by
        unfold muSof
        rw [lintegral_map (hJ.lintegral_prod_right' (ν := (μW'.prod μN).map
          (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r)))) hphi_meas]
        apply lintegral_congr
        intro p
        have hK : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r =>
            ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) *
              γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ) := by
          have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r => (fun i j => ((Matrix.of zz)⁻¹ *
              Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) * γ) i j :
                Formalism.QuantumDeterminants.Mt k r)) := measurable_const
          exact measurable_enorm_composition he0 (meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt zz'))
        show ∫⁻ y, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r) * γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ ∂((μW'.prod μN).map
              (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
                (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))) = _
        rw [lintegral_map hK hphi_meas]
        rfl
    _ = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := rfl

theorem quad_inner1 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN) =
      Lam1 e0 (μW.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t * Matrix.of zz')‖ₑ) :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz)) measurable_id) (meas_const_mt zz'))
  calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN)
      = ∫⁻ s, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz')‖ₑ ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        have hM : (Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hs) hz'
        rw [coef_eq hds hz hs hz', ← hee0 _ hM]
    _ = Lam1 e0 (μW.prod μN) zz zz' := by
        unfold muSof Lam1
        rw [lintegral_map hJ hphi_meas]
        rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_le_I {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) (hw0DD : w0 ∈ DDsp σ w0)
    {e1 : Mx k r → ℂ} (hee1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e1 g = ⟪v, σ g w0⟫_ℂ)
    {zz : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, (fun m : Formalism.QuantumDeterminants.Mt k r => ‖e1 (Matrix.of m)‖ₑ)
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) i j) ∂(μW.prod μN) := by
  have b1 := l_enorm_le (c := c) hds hT hπ hW hN hbe hv hlv hw0DD hz
  refine b1.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr_ae
  filter_upwards [prod_ae hW hN] with p hp
  show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) w0⟫_ℂ‖ₑ =
    ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz)‖ₑ
  rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hz)]

theorem e_weight {e : Mx k r → ℂ} {C a b : ℝ}
    (hb : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e y‖ ≤ C * B.gN y ^ (-a))
    {x : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hpos : 0 < B.gN x) :
    ‖e x‖ₑ * ENNReal.ofReal (B.gN x ^ b) ≤ ENNReal.ofReal |C| * ‖B.gN x ^ (-(a - b))‖ₑ := by
  have h1 := hb x hx
  have h2 : ‖e x‖ * B.gN x ^ b ≤ |C| * B.gN x ^ (-(a - b)) := by
    have e2 : B.gN x ^ (-(a - b)) = B.gN x ^ (-a) * B.gN x ^ b := by
      rw [← Real.rpow_add hpos]
      ring_nf
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpos.le _)))
      (Real.rpow_nonneg hpos.le _)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

def Iint (A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (z : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) ∂μ

def Aext (e : Mx k r → ℂ) (m : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ := ‖e (Matrix.of m)‖ₑ

theorem Aext_meas {e : Mx k r → ℂ} (he : Continuous e) : Measurable (Aext e) := by
  unfold Aext
  exact (Continuous.enorm (he.comp (show Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Matrix.of m) from continuous_id))).measurable

theorem Iint_meas {A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μ] : Measurable (Iint A μ) := by
  unfold Iint
  refine Measurable.lintegral_prod_right' (f := fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
    A (fun i j => (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) i j)) ?_
  refine hA.comp (Continuous.measurable ?_)
  exact ((continuous_snd.fst.matrix_mul continuous_snd.snd).matrix_mul continuous_fst)

theorem unfold_Iint {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {A Ψ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A) (hΨ : Measurable Ψ)
    (hinv : ∀ᵐ z ∂νq, ∀ᵐ p ∂(μW.prod μN),
      Ψ (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) = Ψ z) :
    ∫⁻ z, Iint A (μW.prod μN) z * Ψ z ∂νq = ∫⁻ x, A x * Ψ x ∂μG := by
  have hcont : ∀ z : Formalism.QuantumDeterminants.Mt k r,
      Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    fun z => Continuous.matrix_mul continuous_id continuous_const
  have hg : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul continuous_fst continuous_snd).measurable
  rw [hq (fun x => A x * Ψ x) (hA.mul hΨ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with z hz
  unfold Iint Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [lintegral_map (f := fun s : Formalism.QuantumDeterminants.Mt k r => A (fun i j => (Matrix.of s * Matrix.of z) i j) *
      Ψ (fun i j => (Matrix.of s * Matrix.of z) i j))
    (by exact (hA.comp (hcont z).measurable).mul (hΨ.comp (hcont z).measurable)) hg]
  have hmA : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j)) :=
    hA.comp ((show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul (Continuous.matrix_mul continuous_fst continuous_snd) continuous_const).measurable)
  rw [← lintegral_mul_const _ hmA]
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with p hp
  exact congrArg _ hp.symm

theorem pull2 {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} (F G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (M : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hm : ∀ z, Measurable fun z' => G z' * M z z') :
    ∫⁻ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' ∂νq = K * ∫⁻ z, F z * ∫⁻ z', G z' * M z z' ∂νq' ∂νq := by
  have h1 : ∀ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' = K * (F z * ∫⁻ z', G z' * M z z' ∂νq') := by
    intro z
    have e1 : (fun z' => K * (F z * (G z' * M z z'))) = fun z' => (K * F z) * (G z' * M z z') := by
      funext z'
      ring
    rw [e1, lintegral_const_mul _ (hm z), mul_assoc]
  simp_rw [h1]
  exact lintegral_const_mul' K _ hK

theorem final2 {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hF : Measurable Fx)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG ∂μG = c * ((∫⁻ x, Fx x ∂μG) * ∫⁻ y, Fx y ∂μG) := by
  have h1 : ∀ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG = (c * Fx x) * ∫⁻ y, Fx y ∂μG := by
    intro x
    simp_rw [← mul_assoc]
    exact lintegral_const_mul _ hF
  simp_rw [h1]
  rw [lintegral_mul_const _ (hF.const_mul c), lintegral_const_mul _ hF, mul_assoc]

end Formalism.FourierDecayAlt.P.S3dx4
