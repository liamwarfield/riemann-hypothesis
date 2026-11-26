module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionals

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BaseRepCapelliEigenDual
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

theorem continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (h : B.CkOn m (B.GV k r) f) : ContinuousOn f (B.GV k r) := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat k r) := Matrix.normedSpace
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousWithinAt f' (B.GV k r) g₀ :=
    (hf'.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b
  exact he g a b

end GlobalTheory.CoefZero
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.N1AddEZLe
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : I.card = ∑ i : Fin n, (if i ∈ I then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, eZ]
  split_ifs <;> omega

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 := by
  simp [B.JF, Formalism.QuantumDeterminants.besselJ]

end GlobalTheory.SuppliedPieri
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsCoefContinuousOn
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h.2
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDG ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

end GlobalTheory.SupMeas
end Gp91
end
