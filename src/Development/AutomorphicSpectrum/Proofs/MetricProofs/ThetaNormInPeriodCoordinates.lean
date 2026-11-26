module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem re_dot_sub_re_hermForm {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (ζ : Fin g → ℂ) :
    (ζ ⬝ᵥ (B.map fun x : ℝ => (x : ℂ)).mulVec ζ).re - (hermForm (B.map fun x : ℝ => (x : ℂ)) ζ ζ).re =
      -2 * ((fun i => (ζ i).im) ⬝ᵥ B.mulVec fun i => (ζ i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem periodMatrix_map_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    (GroundTheory.Heights₂.Heights.periodMatrix X Y).map Complex.im = Y := by
  ext i j
  simp [GroundTheory.Heights₂.Heights.periodMatrix]

theorem im_period_point {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (u₁ u₂ : Fin g → ℝ) :
    (fun i => (((GroundTheory.Heights₂.Heights.periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) +
      (fun i => (u₂ i : ℂ))) i).im) = Y.mulVec u₁ := by
  funext i
  simp [GroundTheory.Heights₂.Heights.periodMatrix, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem thetaChar_eq {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (ζ : Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (GroundTheory.Heights₂.Heights.periodMatrix X Y)
        (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) ζ =
      GroundTheory.Heights₂.Heights.thetaChar X Y a c ζ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar GroundTheory.Heights₂.Heights.thetaChar
  refine tsum_congr fun k => ?_
  have e : ((fun i => (k i : ℂ)) + fun i => (a i : ℂ)) =
      fun i => ((intVec k i + a i : ℝ) : ℂ) := by
    funext i
    simp [intVec]
  rw [e]

theorem norm_mul_canTh : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  intro g X Y a c h Hm θ κ _ hY hH hθ u₁ u₂ z hz
  have him := periodMatrix_map_im X Y
  have hinv : GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y) =
      Y⁻¹.map fun x : ℝ => (x : ℂ) := by
    rw [GlobalTheory.CanTh.imInv, him]
  have hq : (fun i => ((h.mulVec z) i).im) = Y.mulVec u₁ := by
    rw [hz]
    exact im_period_point X Y u₁ u₂
  have hdiff := re_dot_sub_re_hermForm Y⁻¹ (h.mulVec z)
  have hcancel : Y⁻¹.mulVec (Y.mulVec u₁) = u₁ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY.det_pos.ne'.isUnit, Matrix.one_mulVec]
  rw [hq, hcancel, dotProduct_comm (Y.mulVec u₁) u₁, ← hinv] at hdiff
  have hqf : u₁ ⬝ᵥ Y.mulVec u₁ = qf Y u₁ := rfl
  rw [hqf] at hdiff
  rw [hθ z, hH z z, norm_mul, GlobalTheory.CanTh.canTh, norm_mul, Complex.norm_exp, thetaChar_eq, thetaNorm,
    ← hz]
  have hre : ((Real.pi / 2 : ℂ) * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z))).re =
      Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re := by
    have : ((Real.pi / 2 : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hre]
  have hexp : Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
      Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
          (h.mulVec z) (h.mulVec z)).re) = Real.exp (-Real.pi * qf Y u₁) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    linear_combination (Real.pi / 2) * hdiff
  calc _ = ‖κ‖ * (‖GroundTheory.Heights₂.Heights.thetaChar X Y a c (h.mulVec z)‖ *
        (Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
          (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
        Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
          (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
            (h.mulVec z) (h.mulVec z)).re))) := by ring
    _ = _ := by rw [hexp]

end GlobalTheory.CompanionTheory.Ar.Nform
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_norm_in_period_coordinates : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh | exact GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh | (intros; apply GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplier
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplier
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.CanThLine

section Law

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_factor {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ) (m n : Fin g → ℤ) {l : Fin g → ℂ}
    (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π / 2 * ((ζ + l) ⬝ᵥ imInv τ *ᵥ (ζ + l)))) *
        (canMult a c m n *
          cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l)) =
      eC (((1 : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec c ⬝ᵥ ofIntVec n)) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ ζ)) *
        cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) := by
  have hl' : l = (fun i => (((m i : ℝ)) : ℂ)) + τ *ᵥ fun i => (((n i : ℝ)) : ℂ) := by
    simpa using hl
  have h1 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) ζ
  have h2 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) l
  rw [← hl'] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ l
  have e0 : (fun i => (((n i : ℝ)) : ℂ)) = ofIntVec n := by
    funext i; simp [ofIntVec]
  have h5 : (l ⬝ᵥ ofIntVec n) = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ τ *ᵥ ofIntVec n := by
    rw [hl, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, ofIntVec]
  have e1 : ((a ⬝ᵥ (fun i => (m i : ℝ)) : ℝ) : ℂ) = ofRealVec a ⬝ᵥ ofIntVec m := by
    simp [dotProduct, ofRealVec, ofIntVec]
  have e2 : ((c ⬝ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) = ofRealVec c ⬝ᵥ ofIntVec n := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [e0] at h1 h2
  rw [canMult, e1, e2]
  simp only [eC, ← Complex.exp_add]
  congr 1
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5,
    dotProduct_comm (ofIntVec n) ζ]
  push_cast
  ring

end Law

section Main

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_mem_thetaLevelChar {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    (fun ζ => cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) * θ (h⁻¹ *ᵥ ζ)) ∈
      GlobalTheory.thetaLevelChar a c 1 τ := by
  have hhi : h * h⁻¹ = 1 := mul_nonsing_inv _ hh
  have hback : ∀ v : Fin g → ℂ, h *ᵥ (h⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hhi, one_mulVec]
  have hd : Differentiable ℂ (fun ζ : Fin g → ℂ => h⁻¹ *ᵥ ζ) :=
    differentiable_pi.2 fun i => by
      simp only [mulVec, dotProduct]
      fun_prop
  refine GlobalTheory.mem_thetaLevelChar.2 ⟨?_, fun n n' z => ?_⟩
  · refine Differentiable.mul ?_ (hθ.comp hd)
    simp only [dotProduct, mulVec]
    fun_prop
  · set l : Fin g → ℂ := (fun i => (n' i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) with hl
    have e : z + τ *ᵥ ofIntVec n + ofIntVec n' = z + l := by
      rw [hl, add_assoc, add_comm (τ *ᵥ _)]
      rfl
    have hL := hlaw n' n (h⁻¹ *ᵥ l) (hback l) (h⁻¹ *ᵥ z)
    rw [hH, hH, hback, hback] at hL
    have hG := gaussian_mul_factor hs hp a c n' n hl z
    simp only [e]
    rw [show h⁻¹ *ᵥ (z + l) = h⁻¹ *ᵥ z + h⁻¹ *ᵥ l from mulVec_add _ _ _, hL]
    linear_combination θ (h⁻¹ *ᵥ z) * hG

theorem eq_const_mul_canTh {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    ∃ κ : ℂ, ∀ z, θ z = κ * canTh τ a c (h *ᵥ z) := by
  have hmem := gaussian_mul_mem_thetaLevelChar hs hp hh hH hθ hlaw
  rw [GlobalTheory.thetaLevelChar_one (a := a) (b := c) (τ := τ) ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, fun z => ?_⟩
  have hback : h⁻¹ *ᵥ (h *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  have hz := congrFun hκ (h *ᵥ z)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  rw [hback] at hz
  rw [canTh, thetaChar_eq_theta, mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add]
  simp

end Main

theorem level_one_line : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  intro g τ h Hm a c θ hs hp hh hH hθ hlaw
  exact eq_const_mul_canTh hs hp hh hH hθ hlaw

end GlobalTheory.CompanionTheory.CanThLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplierStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_canonical_multiplier : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  first | exact @GlobalTheory.CompanionTheory.CanThLine.level_one_line | exact GlobalTheory.CompanionTheory.CanThLine.level_one_line | (intros; apply GlobalTheory.CompanionTheory.CanThLine.level_one_line <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add (f := _)]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add (f := _)]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semicharacter_theta_characteristic : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | exact GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult <;> assumption)
end
end
