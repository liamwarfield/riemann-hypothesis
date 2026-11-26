module

public import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev
public import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.SobolevInterpolation
section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.SobolevMollifier
section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.SobolevDuality
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Duality

variable {s : ℝ}

theorem bessel_ofSchwartz (φ : 𝓢(E, ℂ)) :
    SobolevSpace.bessel s (SobolevSpace.ofSchwartz s φ) =
      (SchwartzMap.fourierMultiplierCLM ℂ (weight s) φ).toLp 2 := by
  apply toTemperedDistribution_injective
  simp only
  rw [SobolevSpace.toDistribution_bessel, SobolevSpace.toDistribution_ofSchwartz,
    Lp.toTemperedDistribution_toLp_eq, besselPotential_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]

end Duality

end

end GroundTheory.Automorphic.Sobolev
end

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section MultiplierFourier

variable {m : E → ℂ} {C s t : ℝ}

end MultiplierFourier

section Convolution



end Convolution

section Mollifier

theorem norm_fourier_le_integral (ψ : 𝓢(E, ℂ)) (ξ : E) :
    ‖(𝓕 ψ : 𝓢(E, ℂ)) ξ‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [SchwartzMap.fourier_coe]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem exists_norm_le_weight (χ : 𝓢(E, ℂ)) (r : ℝ) :
    ∃ C, ∀ ξ : E, ‖χ ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  set n : ℕ := ⌈-r / 2⌉₊
  refine ⟨2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ), fun ξ ↦ ?_⟩
  have h0 : ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := by
    have := SchwartzMap.le_seminorm ℂ 0 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have h1 : ‖ξ‖ ^ (2 * n) * ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ (2 * n) 0 χ := by
    have := SchwartzMap.le_seminorm ℂ (2 * n) 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hb : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
    rcases le_total (‖ξ‖ ^ 2) 1 with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
            have : 0 ≤ (‖ξ‖ ^ 2) ^ n := by positivity
            nlinarith [pow_pos (two_pos (α := ℝ)) n]
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ (2 * ‖ξ‖ ^ 2) ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 2 ^ n * (‖ξ‖ ^ 2) ^ n := by rw [mul_pow]
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by gcongr; linarith
  have key : (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤
      2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) := by
    calc (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) * ‖χ ξ‖ := by gcongr
      _ = 2 ^ n * (‖χ ξ‖ + ‖ξ‖ ^ (2 * n) * ‖χ ξ‖) := by rw [pow_mul]; ring
      _ ≤ _ := by gcongr
  have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ n := by positivity
  have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have := Nat.le_ceil (-r / 2)
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hexp
  calc ‖χ ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖) * ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by
        field_simp
    _ ≤ 2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) *
        ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by gcongr
    _ ≤ _ := by
        gcongr

namespace SobolevSpace

variable {s : ℝ}

@[simp] theorem toDistribution_sub (u v : SobolevSpace E F s) :
    toDistribution (u - v) = toDistribution u - toDistribution v := rfl

end SobolevSpace

end Mollifier

end

end GroundTheory.Automorphic.Sobolev
end

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem one_add_norm_sq_le (ξ η : E) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖ξ - η‖ ^ 2) * (1 + ‖η‖ ^ 2) := by
  have h : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg (ξ - η), norm_nonneg η, sq_nonneg (‖ξ - η‖ - ‖η‖)]
  nlinarith [sq_nonneg ‖ξ - η‖, sq_nonneg ‖η‖, mul_nonneg (sq_nonneg ‖ξ - η‖) (sq_nonneg ‖η‖)]

theorem peetre (r : ℝ) (ξ η : E) :
    (1 + ‖ξ‖ ^ 2) ^ r ≤ 2 ^ |r| * (1 + ‖ξ - η‖ ^ 2) ^ |r| * (1 + ‖η‖ ^ 2) ^ r := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have pζ : (0 : ℝ) < 1 + ‖ξ - η‖ ^ 2 := by positivity
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, ← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pη.le]
    exact Real.rpow_le_rpow pξ.le (one_add_norm_sq_le ξ η) hr
  · rw [abs_of_nonpos hr]
    have key : (1 + ‖η‖ ^ 2) ^ (-r) ≤ 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) * (1 + ‖ξ‖ ^ 2) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pξ.le]
      apply Real.rpow_le_rpow pη.le _ (by linarith)
      have := one_add_norm_sq_le η ξ
      rwa [norm_sub_rev] at this
    rw [Real.rpow_neg pη.le, Real.rpow_neg pξ.le] at key
    have a := Real.rpow_pos_of_pos pξ r
    have b := Real.rpow_pos_of_pos pη r
    have c : 0 < 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) := by positivity
    rw [le_mul_inv_iff₀ a, inv_mul_le_iff₀ b] at key
    calc (1 + ‖ξ‖ ^ 2) ^ r = (1 + ‖ξ‖ ^ 2) ^ r * 1 := (mul_one _).symm
      _ ≤ _ := by nlinarith

end

end GroundTheory.Automorphic.Sobolev
end

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem fourier_char_smul (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  rw [Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3; ring

section Kernel

variable (s N : ℝ) (χ : 𝓢(E, ℂ))

variable {s N}

end Kernel

section Identity

variable {s N : ℝ} (χ : 𝓢(E, ℂ))

end Identity


end

end GroundTheory.Automorphic.Sobolev
