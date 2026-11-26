module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.general_b_fact_version

theorem goal1 :
    ∀ {Y : Type u_1} [inst : NormedAddCommGroup Y] [inst_1 : NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
      {R M : ℝ},
      0 < R →
        DifferentiableOn ℂ g (Metric.ball y (2 * R)) →
          (∀ v ∈ Metric.ball y (2 * R), ‖g v‖ ≤ M) → ‖fderiv ℂ g y‖ ≤ M / R := by
  intro Y _ _ g y R M hR hd hM
  have hy : y ∈ Metric.ball y (2 * R) := Metric.mem_ball_self (by positivity)
  have hmaps : Set.MapsTo g (Metric.ball y (2 * R)) (Metric.closedBall (g y) (2 * M)) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖g v - g y‖ ≤ ‖g v‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM v hv) (hM y hy)
      _ = 2 * M := by ring
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hmaps (by positivity)
  calc ‖fderiv ℂ g y‖ ≤ 2 * M / (2 * R) := h
    _ = M / R := by rw [mul_div_mul_left _ _ (two_ne_zero)]

end Bl.general_b_fact_version
