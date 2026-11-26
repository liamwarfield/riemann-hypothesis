module

public import Formalism.GaussJetBounds.GaussJetProofs.FJEval
public import Formalism.GaussJetBounds.GaussJetProofs.Transfer

@[expose] public section

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Slices

variable {R : Type u} [CommRing R] {T σ ρ : Type}

end Slices

section Rows

end Rows

section Jets

lemma jetPair_monomial_left {K : Type u} [Field K] {ι : Type} (κ : ι →₀ ℕ)
    (F : MvPowerSeries ι K) :
    jetPair (monomial κ (1 : K)) F = ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  rw [jetPair_eq_sum _ _ {κ} (MvPolynomial.support_monomial_subset)]
  simp

end Jets

section Sums

end Sums

section Frames

variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}

def bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then ((x (false, τ.2))⁻¹).transpose else x (false, τ.2)

def bT (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then x τ * (x (false, τ.2)).transpose else 1

end Frames

section Norms

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}

end Norms

end Formalism.DworkPowerSeriesWeights
end
end

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)

end Formalism.DworkPowerSeriesWeights
