module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable (l : ℕ) [Fact l.Prime]

theorem red_norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := norm_l_Cl l

theorem red_norm_natCast {n : ℕ} (h : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 :=
  norm_natCast_Cl_of_not_dvd l h

theorem kur_val {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (l : ℝ) ^ m := by
  obtain ⟨y, hy, hd⟩ := kur_approx l hx ‖x‖ (norm_pos_iff.2 h0)
  have h2 : ‖x‖ = ‖y‖ :=
    norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hd (le_max_left _ _))
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact h0 (norm_eq_zero.1 h2)
  obtain ⟨m, a, -, b, -, ha, hb, e⟩ := kmu_shape l hy hy0
  refine ⟨-m, ?_⟩
  rw [h2, e, norm_mul, norm_div, ha, hb, div_one, mul_one, norm_zpow, norm_l_Cl, inv_zpow, zpow_neg]

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.LatModel
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

structure LatModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) :
    Prop where
  eq2 : g2 = ι L.g₂
  eq3 : g3 = ι L.g₃
  n2 : ‖g2‖ ≤ 1
  n3 : ‖g3‖ ≤ 1

end ReciprocityTheory.ChartRestriction.L1
end
end
