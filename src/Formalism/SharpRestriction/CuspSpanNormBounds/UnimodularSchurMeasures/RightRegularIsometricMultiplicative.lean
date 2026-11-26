module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def UnimodA (X : CData) : Prop := (X.I.muA X.μf).IsMulRightInvariant

instance rr_muG_right {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsMulRightInvariant :=
  ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

instance rr_muG_haar {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsHaarMeasure := by
  unfold Formalism.REAL.muG; infer_instance

theorem rr_rep_eq_rep (I : AutInst) (fund : Set I.GA) (y : I.GA) : I.rep fund y = rr_rep I.GFset fund y := rfl

theorem rr_muA_left (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant] :
    (I.muA μf).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

theorem rr_muA_right (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulRightInvariant] :
    (I.muA μf).IsMulRightInvariant :=
  Measure.prod.instIsMulRightInvariant

theorem rr_muA_sigmaFinite (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] : SigmaFinite (I.muA μf) := by
  unfold AutInst.muA; infer_instance

theorem rr_FD_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : rr_FD (I.muA μf) (rr_GF I) fund :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem rr_IsReg_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (h : I.IsRightReg μf fund R) :
    rr_IsReg (I.muA μf) (rr_GF I) fund R := h

def RepAlg (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ ∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖

def RegData (X : CData) : Prop :=
  X.μf.IsHaarMeasure ∧ X.I.IsFundDom (X.I.muA X.μf) X.fund ∧ X.I.IsRightReg X.μf X.fund X.R

theorem rightRegular_isometric_multiplicative (X : CData) (hd : RegData X) (hu : UnimodA X) : RepAlg X := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have h1 := rr_FD_of X.I X.μf X.fund hF
  have h2 := rr_IsReg_of X.I X.μf X.fund X.R hR
  exact ⟨fun g k => rr_mul h1 h2 g k, rr_one h1 h2, fun g F => rr_norm h1 h2 g F⟩

theorem regular_rep_coeff_measurable (X : CData) (hd : RegData X) (hu : UnimodA X) (x y : X.L2) :
    StronglyMeasurable fun g => ⟪x, X.R g y⟫_ℂ := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  exact rr_weak_meas (rr_FD_of X.I X.μf X.fund hF) (rr_IsReg_of X.I X.μf X.fund X.R hR) x y

end Formalism.MainNotions.LeviCoordinates

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem discrete_series_unitary_rep {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : CayleySignature.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      σ (x * y) = (σ x).comp (σ y)) ∧ ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, -, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hback : ∀ x : CayleySignature.Mat k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPi, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
    show (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) = Formalism.REAL.Jm ε
    have e1 : (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) =
        (P⁻¹)ᴴ * (xᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * x) * P⁻¹ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, hPJ, hx', ← hPJ]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPi']; simp
  refine ⟨?_, fun x hx y hy => ?_, fun x hx v => ?_⟩
  · have : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hPi] at this
  · have := hmul _ (hmem x hx) _ (hmem y hy)
    simp only [hback] at this
    have e : P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = x * y := by
      calc P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = (P⁻¹ * P) * x * (P⁻¹ * P) * y * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = x * y := by rw [hPi]; simp
    rwa [e] at this
  · have := hiso _ (hmem x hx) v
    simp only [hback] at this
    exact this

section Pos

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (σ : CayleySignature.Mat k r → (H →L[ℂ] H))
  (hmul : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (x * y) = (σ x).comp (σ y))
  (hone : σ 1 = 1)

include hmul in
theorem smooth_vectors_translate {ai : CayleySignature.Mat k r} (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) : σ ai v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hv (g₀ * ai) (mat_mul_mem_UH_Hpk hg₀ hai)
  let L : CayleySignature.Mat k r →L[ℝ] CayleySignature.Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ ai)
  have hL : ∀ g, L g = g * ai := fun g => rfl
  refine ⟨L ⁻¹' Uo, fun g => F (L g), hO.preimage L.continuous, hmem, ?_, fun g hg hin => ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun g hg => hg)
  · have h1 : σ (g * ai) v = F (g * ai) := hEq (g * ai) hg (mat_mul_mem_UH_Hpk hin hai)
    show σ g (σ ai v) = F (L g)
    rw [hL, ← h1, hmul g hin ai hai]; rfl


end Pos

end Formalism.MainNotions.LeviCoordinates

end
end
