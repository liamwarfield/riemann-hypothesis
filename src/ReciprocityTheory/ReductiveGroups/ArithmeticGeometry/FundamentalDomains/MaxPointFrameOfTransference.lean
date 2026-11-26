module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeBoundAtMaximumOfTransference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalChartNormControlHolds

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMax
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NonvanishingNearHalfMax : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 x0 : Frame X.Ψ r) (w : ℝ),
    X.IsSec la P → z0 ∈ X.dom → X.IsOrtho x0 → (∃ b ∈ Bor X.Ψ r, x0 = rmul z0 b) →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r →
    ∀ Z : X.Coord, X.zN Z ≤ frameRadius w r / 5 → P (X.xZ x0 Z) ≠ 0

def FrameAtHalfMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 : Frame X.Ψ r) (laStar w : ℝ),
    X.IsSec la P → z0 ∈ X.dom →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r → 0 < laStar → laStar ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (x : Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.dom ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar (3 * frameRadius w r / 5)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, X.maj x τ v ≤ 2 * X.maj z0 τ v

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMaxHolds
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem nonvanishingNearHalfMax_holds : NonvanishingNearHalfMax (E := E) := by
  unfold NonvanishingNearHalfMax
  intro r X la P z0 x0 w hSec hz0 hx0o ⟨b, hb, hx0⟩ hmax hpos hw hw1 hr Z hZ hPZ
  have hx0d : x0 ∈ X.dom := by rw [hx0]; exact OrthogonalFrameDomain.rmul_mem_dom (X := X) hz0 hb
  have hpx : X.pnorm la P x0 = X.pnorm la P z0 := by
    rw [hx0]; exact FrameDegreeData.pnorm_rmul (X := X) la P hSec.2.1 z0 hz0 b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun y => rfl
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
  have hw0 : w ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hwr : 0 < w * r := by nlinarith
  have hwr1 : 1 ≤ w * r := by nlinarith
  have hsq : Real.sqrt (w * r) ^ 2 = w * r := Real.sq_sqrt hwr.le
  have hs1 : 1 ≤ Real.sqrt (w * r) := by nlinarith [Real.sqrt_nonneg (w * r)]
  set ρ := frameRadius w r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, frameRadius]; positivity
  have hρle : ρ ≤ 1 / 10 := by
    rw [hρdef, frameRadius]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hρsq : 4 * w * r * ρ ^ 2 = 1 / 25 := by
    rw [hρdef, frameRadius, div_pow, mul_pow, hsq]
    field_simp
    ring
  have hM0 : 0 < ‖P x0‖ := by
    have h1 : 0 < X.pnorm la P x0 := hpx ▸ hpos
    rw [hpn] at h1
    rcases (norm_nonneg (P x0)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h1
      exact absurd h1 (lt_irrefl 0)
  have hzt : ∀ t : ℂ, ‖t‖ < 5 → X.zN (t • Z) ≤ ρ := fun t ht =>
    (OrthogonalFrameDomain.zN_smul_le (X := X) t Z).trans (by nlinarith [OrthogonalFrameDomain.zN_nonneg (X := X) Z, norm_nonneg t])
  have hdom : ∀ t : ℂ, ‖t‖ < 5 → X.xZ x0 (t • Z) ∈ X.dom := fun t ht =>
    OrthonormalChartBounds.xZ_mem_dom (X := X) hx0d hx0o (lt_of_le_of_lt (hzt t ht) (by linarith))
  have hbound : ∀ t : ℂ, ‖t‖ < 5 → ‖P (X.xZ x0 (t • Z))‖ < 3 * ‖P x0‖ := by
    intro t ht
    have hyd := hdom t ht
    have hny := BoundedSectionAlgebra.nfac_pos (X := X) hyd la
    have hnx := BoundedSectionAlgebra.nfac_pos (X := X) hx0d la
    have hlog := OrthonormalChartBounds.nfac_xZ (X := X) hx0d hx0o hρpos hρle (hzt t ht) la w hw
    have hz2 : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 25 := by
      rw [← hρsq]
      have hwr4 : 0 ≤ 4 * w * r := by nlinarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (OrthogonalFrameDomain.zN_nonneg (X := X) _) (hzt t ht) 2) hwr4
    have hlow : Real.log (X.nfac la x0) - 1 / 25 ≤ Real.log (X.nfac la (X.xZ x0 (t • Z))) := by
      have := (abs_le.mp (hlog.trans hz2)).1
      linarith
    have hexp : X.nfac la x0 * Real.exp (-(1 / 25)) ≤ X.nfac la (X.xZ x0 (t • Z)) := by
      rw [← Real.exp_log hnx, ← Real.exp_log hny, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpy : X.pnorm la P (X.xZ x0 (t • Z)) ≤ 2 * X.pnorm la P x0 := by
      rw [hpx]; exact hmax _ hyd
    rw [hpn, hpn] at hpy
    have h1 : ‖P (X.xZ x0 (t • Z))‖ * (X.nfac la x0 * Real.exp (-(1 / 25))) ≤
        2 * (‖P x0‖ * X.nfac la x0) :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hpy
    have h2 : ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) ≤ 2 * ‖P x0‖ := by
      have h3 : (‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25))) * X.nfac la x0 ≤
          (2 * ‖P x0‖) * X.nfac la x0 := by nlinarith
      exact le_of_mul_le_mul_right h3 hnx
    have hE : Real.exp (-(1 / 25)) * Real.exp (1 / 25) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : ‖P (X.xZ x0 (t • Z))‖ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) := by
      calc ‖P (X.xZ x0 (t • Z))‖
          = ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) * Real.exp (1 / 25) := by
            rw [mul_assoc, hE, mul_one]
        _ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have he := OrthogonalFrameDomain.exp_small
    nlinarith [mul_lt_mul_of_pos_left he hM0]
  have h5 : ∀ s ∈ Metric.ball (1 : ℂ) 4, ‖s‖ < 5 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 5 := by rw [norm_one]; linarith
  set g : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hg
  have hg1 : g 1 = 0 := by simp only [hg, one_smul]; exact hPZ
  have hg0 : g 0 = P x0 := by simp only [hg, zero_smul, (OrthogonalFrameDomain.xZ_zero (X := X))]
  have hgd : DifferentiableOn ℂ g (Metric.ball 1 4) := by
    intro t ht
    have hin : DifferentiableAt ℂ (fun s : ℂ => X.xZ x0 (s • Z)) t :=
      (OrthogonalFrameDomain.xZ_diff (X := X) x0).differentiableAt.comp t (differentiableAt_id.smul_const Z)
    exact (hSec.1 _ (hdom t (h5 t ht))).comp t hin.differentiableWithinAt
      (fun s hs => hdom s (h5 s hs))
  have hmaps : Set.MapsTo g (Metric.ball 1 4) (Metric.closedBall (g 1) (3 * ‖P x0‖)) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm, hg1, sub_zero]
    exact (hbound s (h5 s hs)).le
  have hd : dist (0 : ℂ) 1 = 1 := by simp [dist_eq_norm]
  have h0 : (0 : ℂ) ∈ Metric.ball (1 : ℂ) 4 := by rw [Metric.mem_ball, hd]; norm_num
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps h0
  rw [hg0, hg1, dist_zero_right, hd, mul_one] at hS
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem maxPointFrame_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtHalfMaximum (E := E) := by
  intro r X la P z0 laStar w hSec hz0 hmax hpos hw hw1 hr hla0 hla1 hL'
  obtain ⟨hO, -, hSF⟩ := orthonormalFlagTranslate_holds (E := E) r X.toData
  obtain ⟨b, hb, hob⟩ := hO z0 hz0
  have hx0 : rmul z0 b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X.toData) hz0 hb
  have hsf : X.SameFlag z0 (rmul z0 b) := FlagSpanBounds.sameFlag_rmul (X := X.toData) z0 hb
  have hmaj : X.maj z0 = X.maj (rmul z0 b) := (hSF z0 hz0 (rmul z0 b) hx0 hsf).2

  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hwr : 1 ≤ w * (r : ℝ) := by nlinarith
  have hsq : 1 ≤ Real.sqrt (w * r) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hwr
  have hρpos : 0 < frameRadius w r := by
    unfold frameRadius
    have : 0 < 10 * Real.sqrt (w * r) := by linarith
    positivity
  have hρle : frameRadius w r ≤ 1 / 10 := by
    unfold frameRadius
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)

  obtain ⟨lam, Z, hZ, hlam⟩ := h41a r X z0 (rmul z0 b) laStar (3 * frameRadius w r / 5) hz0 hx0 hob hsf
    hla0 hla1 (by linarith) (by linarith) hL'
  have hZ' : X.zN Z ≤ frameRadius w r / 5 := by linarith

  obtain ⟨hloc, -⟩ := h6p1 r X.toData (rmul z0 b) hx0 hob (frameRadius w r / 5) (by linarith) (by linarith)
  obtain ⟨hxdom, -, hmajb⟩ := hloc Z hZ'

  have hP : P (X.xZ (rmul z0 b) Z) ≠ 0 :=
    nonvanishingNearHalfMax_holds (E := E) r X.toData la P z0 (rmul z0 b) w hSec hz0 hob ⟨b, hb, rfl⟩ hmax hpos hw hw1 hr Z hZ'
  have hden : 0 < 1 - frameRadius w r / 5 := by linarith
  have hc : (1 + frameRadius w r / 5) / (1 - frameRadius w r / 5) ≤ 2 := by
    rw [div_le_iff₀ hden]; linarith
  refine ⟨X.xZ (rmul z0 b) Z, lam, hxdom, hlam, hP, fun τ v => ?_⟩
  have hm : 0 ≤ X.maj (rmul z0 b) τ v := FlagSpanBounds.maj_nonneg (X := X.toData) hx0 τ v
  calc X.maj (X.xZ (rmul z0 b) Z) τ v
      ≤ (1 + frameRadius w r / 5) / (1 - frameRadius w r / 5) * X.maj (rmul z0 b) τ v := ((hmajb τ v).2)
    _ ≤ 2 * X.maj (rmul z0 b) τ v := mul_le_mul_of_nonneg_right hc hm
    _ = 2 * X.maj z0 τ v := by rw [hmaj]

theorem maxPointFrame_of_transference (hD5 : CoveringRadiusStatement) : FrameAtHalfMaximum (E := E) := maxPointFrame_of_lower_bound (latticeBoundAtMaximum_of_transference hD5) orthonormalChartNormControl_holds

end ReciprocityTheory.ChartRestriction.G.FD
